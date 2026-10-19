"""Recompute editorial checks; does not run Lean. Author: Juan Pablo Traverso Gianini."""
from pathlib import Path
import re,collections,json,hashlib,sys
W=Path(sys.argv[1]).resolve()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def norm(x):return re.sub(r'\s|[.,;]','',x)
def displays(s):return collections.Counter(norm(x) for x in re.findall(r'\\\[(.*?)\\\]',s,re.S))
def inline(s):return set(norm(x) for x in re.findall(r'\\\((.*?)\\\)',s,re.S))
def heads(s):return re.findall(r'^#+ ((?:Theorem|Lemma|Proposition|Corollary|Teorema|Lema|Proposición|Corolario|Problem|Problema) [^\n]+)',s,re.M)
all_results=[]
for n,v in [('I','1.4'),('II','1.3'),('III','1.6')]:
 P=W/f'edition/PAPER_{n}';checks=[];records=[]
 for lang in ['en','es']:
  original=W/f'baseline/PAPER_{n}_{lang}.md'; main=P/f'01_manuscript/PAPER_{n}_preprint_v{v}_{lang}.md';comp=P/f'05_formalization/FORMALIZATION_COMPANION_v{v}_{lang}.md'
  o=original.read_text(encoding='utf-8');s=main.read_text(encoding='utf-8');c=comp.read_text(encoding='utf-8');both=s+'\n'+c
  missing=list((displays(o)-displays(both)).elements())
  imissing=sorted(inline(o)-inline(both))
  ids=lambda t:set(re.findall(r'(?<!`)`([^`\n]+)`(?!`)',t))
  # PASS in front-matter is historical audit status, not a theorem identifier.
  idmissing=sorted(ids(o)-ids(both)-{'PASS'})
  checks.extend([{'id':lang+'-displays','pass':not missing,'baseline_count':sum(displays(o).values()),'missing':missing},{'id':lang+'-inline-math','pass':not imissing,'missing':imissing},{'id':lang+'-result-headings','pass':heads(o)==heads(s),'count':len(heads(o))},{'id':lang+'-declaration-traceability','pass':not idmissing,'missing':idmissing}])
  for p in [main,comp]:
   tex=p.with_suffix('.tex');pdf=p.with_suffix('.pdf');log=p.with_suffix('.log')
   text=log.read_text(encoding='utf-8',errors='replace')
   bad=[l for l in text.splitlines() if any(z in l for z in ['Overfull','Missing character','Undefined control sequence','LaTeX Error','undefined references'])]
   wrapper=(P/'02_validation'/f'{p.stem}_compile.txt').read_text(encoding='utf-8')
   generated=('Output written on '+p.stem+'.xdv') in text and ('Writing `'+p.stem+'.pdf`') in wrapper and pdf.stat().st_mtime>=tex.stat().st_mtime and pdf.read_bytes().startswith(b'%PDF-')
   checks.append({'id':p.stem+'-compiler','pass':not bad and generated,'diagnostics':bad,'engine':'Tectonic XeTeX + xdvipdfmx','pdf_output_confirmed':generated})
   records.append({'file':p.relative_to(P).as_posix(),'md_sha256':sha(p),'tex_sha256':sha(tex),'pdf_sha256':sha(pdf),'log_sha256':sha(log)})
  # A removed paragraph is either moved to the companion or listed for manual delta review.
  changed=[p for p in o.split('\n\n') if p.strip() and p not in both]
  (P/'02_validation'/f'PARAGRAPHS_FOR_REVIEW_{lang}.json').write_text(json.dumps(changed,ensure_ascii=False,indent=2),encoding='utf-8')
  (P/'02_validation'/f'BASELINE_HASH_{lang}.json').write_text(json.dumps({'baseline_sha256':sha(original),'main_sha256':sha(main),'companion_sha256':sha(comp),'changed_paragraphs':len(changed)},indent=2),encoding='utf-8')
 # Compare stable result IDs across languages, allowing translated descriptor text.
 texts=[(P/f'01_manuscript/PAPER_{n}_preprint_v{v}_{l}.md').read_text(encoding='utf-8') for l in ['en','es']]
 hids=lambda t:re.findall(r'^#+ (?:Theorem|Lemma|Proposition|Corollary|Teorema|Lema|Proposición|Corolario|Problem|Problema) ([A-E]?\.?\d+(?:\.\d+)*)',t,re.M)
 checks.append({'id':'bilingual-result-identifiers','pass':hids(texts[0])==hids(texts[1]),'en':hids(texts[0]),'es':hids(texts[1])})
 checks.append({'id':'bilingual-figures','pass':len(re.findall(r'!\[',texts[0]))==len(re.findall(r'!\[',texts[1]))})
 result={'paper':n,'version':v,'checks':checks,'artifacts':records,'status':'PASS' if all(x['pass'] for x in checks) else 'FAIL'}
 (P/'02_validation/AUTOMATED_CHECKS.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
 all_results.append(result)
 print(n,result['status'],[x for x in checks if not x['pass']],flush=True)
(W/'control/AUDIT_SUMMARY.json').write_text(json.dumps(all_results,ensure_ascii=False,indent=2),encoding='utf-8')
