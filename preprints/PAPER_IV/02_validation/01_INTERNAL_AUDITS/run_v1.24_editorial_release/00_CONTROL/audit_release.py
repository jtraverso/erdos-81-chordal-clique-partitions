"""Documentary audit only: no Lean/Lake process is started.

Usage: python audit_release.py EDITION V123_MANUSCRIPTS APPROVED_LOCAL FREEZE OUTPUT
Requires PyMuPDF on PYTHONPATH. Paths are input arguments, not published evidence.
"""
from pathlib import Path
from collections import Counter
import sys, re, json, hashlib, zipfile, difflib
import fitz

ROOT, BASE, LOCAL, FREEZE, OUT = map(Path, sys.argv[1:])
OUT.mkdir(parents=True, exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:p.read_text(encoding='utf-8-sig')
write=lambda name,x:(OUT/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
math=lambda s:re.findall(r'\\\[.*?\\\]|\\\(.*?\\\)',s,re.S)
disp=lambda s:re.findall(r'\\\[.*?\\\]',s,re.S)
heads=lambda s:re.findall(r'^(?:### |\*\*)(?:Theorem|Corollary|Lemma|Proposition|Teorema|Corolario|Lema|Proposición) [A-Z0-9][^\n]*',s,re.M)
def unbox(s):
    pos=0
    while (start:=s.find(r'\boxed{',pos))>=0:
        op=start+len(r'\boxed');depth=1;i=op+1
        while depth:
            if s[i]=='{' and s[i-1]!='\\':depth+=1
            if s[i]=='}' and s[i-1]!='\\':depth-=1
            i+=1
        content=s[op+1:i-1];trim=content.rstrip()
        if trim and trim[-1] in '.,;':s=s[:op+1]+trim[:-1]+content[len(trim):]+'}'+trim[-1]+s[i:]
        pos=i+1
    return s
issues=[];semantic=[];docs=[];texts={}
renders={r['pdf']:r for r in json.loads(read(ROOT/'02_validation/RENDER_BINDING.json'))}
for lang in ['en','es']:
    old=read(BASE/f'PAPER_IV_preprint_v1.23_{lang}.md')
    main=read(ROOT/f'01_manuscript/PAPER_IV_preprint_v1.24_{lang}.md')
    comp=read(ROOT/f'05_formalization/FORMALIZATION_COMPANION_v1.24_{lang}.md')
    od=list(map(unbox,disp(old)));nd=disp(main)
    extra=list((Counter(nd)-Counter(od)).elements())
    checks={'237_displays_preserved':len(od)==237 and not Counter(od)-Counter(nd),
      '238_displays_after':len(nd)==238,
      'existing_F5_premise_only':len(extra)==1 and '2(1-\\delta_{11}/4)' in extra[0],
      'original_display_order':len(extra)==1 and [x for x in nd if x!=extra[0]]==od,
      'labels_unchanged':re.findall(r'\\tag\{([^}]+)\}',old)==re.findall(r'\\tag\{([^}]+)\}',main),
      '33_named_headings_unchanged':heads(old)==heads(main) and len(heads(old))==33,
      'literal_Lean_excerpts_preserved':re.findall(r'```lean\n(.*?)```',old,re.S)==re.findall(r'```lean\n(.*?)```',comp,re.S),
      'main_has_no_Lean_code_fences':not re.findall(r'```lean',main)}
    semantic.append({'language':lang,'baseline_sha256':sha(BASE/f'PAPER_IV_preprint_v1.23_{lang}.md'),'checks':checks})
    issues += [f'{lang}: {k}' for k,v in checks.items() if not v]
    for folder,stem,localstem in [('01_manuscript','PAPER_IV_preprint_v1.24','PAPER_IV_v1.24'),('05_formalization','FORMALIZATION_COMPANION_v1.24','FORMALIZATION_COMPANION_v1.24')]:
        p=ROOT/folder/f'{stem}_{lang}.md';body=read(p);tex=p.with_suffix('.tex');pdf=p.with_suffix('.pdf');tt=read(tex)
        texts[(folder,lang)]=body
        prior=read(LOCAL/folder/f'{localstem}_{lang}.md')
        if list(map(unbox,math(prior)))!=math(body):issues.append(f'math changed after local audit: {p.name}')
        (OUT/f'DIFF_V123_TO_V124_{lang}.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),main.splitlines(True),fromfile=f'v1.23/{lang}',tofile=f'v1.24/{lang}')),encoding='utf-8')
        log=read(p.with_suffix('.log'))+'\n'+read(ROOT/'02_validation'/f'{pdf.stem}_compile.txt')
        problems=re.findall(r'Overfull[^\n]*|Missing character:[^\n]*|[^\n]*undefined[^\n]*',log,re.I)
        if problems:issues.append(f'typesetting: {p.name}')
        d=fitz.open(pdf);pdftext='\n'.join(pg.get_text() for pg in d)
        refs=set(re.findall(r'^\[(\d+)\]',body,re.M));cited=set()
        before=re.split(r'^## (?:References|Referencias)',body,flags=re.M)[0]
        for cit in re.findall(r'\[(\d+(?:[–,-]\d+)*)(?:, [^\]]+)?\]',before):
            for a,b in re.findall(r'(\d+)(?:[–-](\d+))?',cit):cited.update(str(i) for i in range(int(a),int(b or a)+1))
        rr=renders[pdf.relative_to(ROOT).as_posix()]
        pkgs=[q for x in re.findall(r'\\usepackage(?:\[[^\]]*\])?\{([^}]+)\}',tt) for q in x.split(',')]
        checks={'render_hash':rr['sha256']==sha(pdf),'no_clipping_flags':not rr['page_clipping_flags'],
          'compiled_final_tex':pdf.stat().st_mtime>=tex.stat().st_mtime,'compiler_names_pdf':pdf.name in log,
          'no_missing_citations':not(cited-refs),'no_duplicate_packages':max(Counter(pkgs).values())==1,
          'no_local_review_status':not re.search(r'Local editorial review|Revisión editorial local|draft remains subject|borrador queda sujeto',body+'\n'+tt+'\n'+pdftext),
          'no_private_paths':not re.search(r'[A-Z]:[\\/]Users[\\/]|OneDrive - Camara',body+'\n'+tt),
          'no_escaped_space_url_macro':not re.search(r'\\nolinkurl\{[^}]*\\ ',tt)}
        issues += [f'{p.name}: {k}' for k,v in checks.items() if not v]
        docs.append({'file':p.relative_to(ROOT).as_posix(),'md_sha256':sha(p),'tex_sha256':sha(tex),'pdf_sha256':sha(pdf),'pages':len(d),'checks':checks,'typesetting_errors':problems})
parity=[]
for folder in ['01_manuscript','05_formalization']:
    norm=lambda s:re.sub(r'\s+','',re.sub(r'\\text\{[^}]*\}',r'\\text{LANG}',s))
    a,b=(texts[(folder,l)] for l in ['en','es'])
    ma,mb=(list(map(norm,math(t))) for t in [a,b])
    ok=Counter(ma)==Counter(mb)
    parity.append({'document':folder,'en_fragments':len(ma),'es_fragments':len(mb),'math_multiset_identical':ok,'ordered_identical':ma==mb,'note':'The single translated inline z occurrence has different prose order; mathematical multisets agree.'})
    if not ok:issues.append(f'bilingual math: {folder}')
source=FREEZE/'05_formalization/lean_piv-v12-fb459343d234';archive=FREEZE/'05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip'
assert sha(archive)=='cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6'
sources=[]
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        if name.endswith('.lean'):
            assert z.read(name)==(source/name).read_bytes(),name
            sources.append({'path':name,'sha256':sha(source/name)})
assert len(sources)==607
scope=json.loads(read(source/'FREEZE_SCOPE.json'));logs=[];total=0
run=FREEZE/'03_reproducibility/full_rebuild_v12_20260929_resume/combined/modules'
for target in scope['targets']:
    p=run/(target+'.log');e=run/(target+'.exit');s=read(p)
    assert read(e).strip()=='EXIT_CODE=0'
    ax=re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]',s)
    for names in ax:assert set(x.strip() for x in names.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
    total+=len(ax);logs.append({'target':target,'log_sha256':sha(p),'exit_sha256':sha(e),'historical_exit_code':0,'axiom_outputs':len(ax)})
assert total==461 and len(logs)==19
assert len(re.findall(r'^#check ',read(source/'ReleaseExportCheck.lean'),re.M))==224
annex=FREEZE/'05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip'
assert sha(annex)=='2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d'
write('FROZEN_IDENTITY.json',{'status':'PASS','Lean_or_Lake_executed':False,'archive_sha256':sha(archive),'annex_archive_sha256':sha(annex),'source_manifest_sha256':sha(FREEZE/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'),'files':sources,'historical_logs':logs,'axiom_outputs':total,'export_checks':224})
result={'status':'PASS' if not issues else 'FAIL','scope':'Editorial invariants and historical freeze identity; no fresh kernel execution, bibliography search or independent proof audit. Visual judgment is recorded separately.','semantic':semantic,'documents':docs,'bilingual':parity,'issues':issues}
write('AUTOMATED_CHECKS.json',result)
print(json.dumps({'status':result['status'],'issues':issues,'pages':sum(d['pages'] for d in docs),'Lean_files':607,'historical_targets':19}))
sys.exit(bool(issues))
