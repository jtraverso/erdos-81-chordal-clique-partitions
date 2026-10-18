"""Static final-publication checks. This does not replace Lean or visual review.

Copyright 2026 Juan Pablo Traverso Gianini
SPDX-License-Identifier: Apache-2.0"""
from pathlib import Path
import json, re, hashlib, zipfile, sys
from urllib.parse import unquote

ROOT=Path(__file__).resolve().parents[2]
fail=[]; checks=[]; count={'documents':0,'lean_files':0,'files':0,'archives':0}
def check(ok,label,detail=''):
    checks.append({'check':label,'passed':bool(ok),'detail':detail})
    if not ok:fail.append(label+(': '+detail if detail else ''))
def lean_code(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2;continue
        if depth:
            if s[i:i+2]=='-/':depth-=1;i+=2
            else:i+=1
            continue
        if s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j;continue
        if s[i]=='"':
            i+=1
            while i<len(s):
                if s[i]=='\\':i+=2;continue
                if s[i]=='"':i+=1;break
                i+=1
            continue
        out.append(s[i]);i+=1
    return ''.join(out)
private=re.compile(r'C:(?:[/\\]+)Users(?:[/\\]+)jtraverso|Camara de Comercio de Santiago|CCS_NOTEBOOK',re.I)
for w in json.loads((ROOT/'PUBLICATION_INDEX.json').read_text(encoding='utf-8'))['works']:
    key=w['work'];p=ROOT/w['path']
    for needed in ['README.md','LICENSE','LICENSE.md','CITATION.cff','index.html']:
        check((p/needed).is_file(),key+' scaffold '+needed)
    for role,folder,stem in [('main','01_manuscript',w['main_stem']),('companion','05_formalization',w['companion_stem'])]:
        for lang in ['en','es']:
            for ext in ['md','tex','pdf']:
                f=p/folder/(stem+'_'+lang+'.'+ext)
                check(f.is_file(),key+' '+role+' '+lang+' '+ext)
            f=p/folder/(stem+'_'+lang+'.md')
            if not f.exists():continue
            s=f.read_text(encoding='utf-8');count['documents']+=1
            check('1.0' in s[:1800],key+' '+role+' '+lang+' version1.0')
            bad=re.findall(r'Working draft|borrador de trabajo|draft remains subject|EDITORIAL_DRAFT|Status:.*DRAFT|computational revision 2|candidate contributions',s,re.I)
            check(not bad,key+' '+role+' '+lang+' no draft marks',str(bad))
            check(not private.search(s),key+' '+role+' '+lang+' portable text')
    license_files=list((p/'05_formalization').rglob('LICENSE'))
    check(any('Apache License' in x.read_text(encoding='utf-8',errors='ignore') for x in license_files),key+' Apache source license')
    leaks=[];escapes=[];archive_leaks=[];large=[]
    for f in p.rglob('*'):
        if not f.is_file():continue
        count['files']+=1
        rel=f.relative_to(p).as_posix()
        if '.lake' in f.parts or f.suffix in ['.olean','.ilean','.pyc','.exe']:fail.append(key+' compiled/cache file '+rel)
        if f.stat().st_size>95*1024**2:large.append(rel)
        if f.suffix=='.zip':
            count['archives']+=1
            with zipfile.ZipFile(f) as z:
                for name in z.namelist():
                    if name.endswith('/'):continue
                    try:s=z.read(name).decode('utf-8-sig')
                    except UnicodeError:continue
                    if private.search(s):archive_leaks.append(rel+'!'+name)
            continue
        try:s=f.read_text(encoding='utf-8-sig')
        except UnicodeError:continue
        if private.search(s):leaks.append(rel)
        if f.suffix=='.lean':
            count['lean_files']+=1
            if re.search(r'\b(sorry|admit|axiom|native_decide)\b',lean_code(s)):escapes.append(rel)
    check(not leaks,key+' no workstation paths',str(leaks))
    check(not archive_leaks,key+' archive privacy',str(archive_leaks))
    check(not escapes,key+' no Lean proof escape hatches',str(escapes))
    check(not large,key+' GitHub file size',str(large))
    # Current public-facing navigation must resolve within the staged tree.
    broken=[]
    nav=[p/'README.md',p/'index.html']
    nav+=list((p/'01_manuscript').glob('*.md'))+list((p/'05_formalization').glob('*v1.0*.md'))
    for f in nav:
        if not f.exists():continue
        s=f.read_text(encoding='utf-8')
        links=re.findall(r'\]\(([^)]+)\)',s)+re.findall(r'href="([^"]+)"',s)
        for link in links:
            link=unquote(link.split('#')[0].strip('<>'))
            if not link or re.match(r'\w+:',link):continue
            if not (f.parent/link).exists():broken.append(f.relative_to(p).as_posix()+':'+link)
    check(not broken,key+' local navigation',str(broken))
report={'status':'PASS_STATIC_PUBLICATION' if not fail else 'FAIL','scope':'Static release integrity, privacy, exact filenames, navigation, and proof escape-hatch scan; build and rendered QA are separate evidence.','counts':count,'checks':checks,'failures':fail}
out=ROOT/'publication'/'preprint1.0';out.mkdir(parents=True,exist_ok=True)
(out/'STATIC_AUDIT.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':report['status'],'counts':count,'failures':fail},ensure_ascii=True,indent=2))
sys.exit(bool(fail))
