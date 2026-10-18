"""Adversarial finite certificates; greedy completion is not the HJ proof."""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
import importlib.util,json,gzip,shutil,hashlib
from verify_v06 import verify
R=Path(__file__).resolve().parent;D=R/'certificates';D.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('legacy_generator',R/'historical_generator.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
rows=[]
def save(label,d):
    result=verify(d);p=D/(label+'.json.gz');p.write_bytes(gzip.compress(json.dumps(d,separators=(',',':')).encode(),mtime=0));rows.append({'label':label,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),**result})

for p,q,h,shape in [(18,36,1,'saturated_matching'),(19,37,1,'three_edit_classes'),(19,39,1,'three_edit_classes'),(37,73,2,'concentrated_stars'),(37,74,2,'dense_outer_cycle'),(37,75,2,'concentrated_stars')]:
    E=g.complete_split(p,q)
    if shape=='saturated_matching':E|=set(zip(range(p,p+q,2),range(p+1,p+q,2)))
    elif shape=='three_edit_classes':
        E.remove((0,1));E.remove((2,p));E|=set(zip(range(p+1,p+q-1,2),range(p+2,p+q,2)))
    elif shape=='concentrated_stars':
        E-={(0,1),(0,2),(3,p),(3,p+1)};E|={(p+2,p+3),(p+2,p+4),(p+5,p+6),(p+5,p+7)}
    else:
        E|={(x,x+1) for x in range(p,p+q-1)}|{(p,p+q-1)}
    assert g.parameters(p,q,E)['h']==h
    for mode in ['all_k4','triangles']:save(f'{p}_{q}_{shape}_{mode}',g.construct(p,q,E,mode,601+len(rows)))
for q in [125,126,127]:
    p=63;E=g.complete_split(p,q);E.remove((0,1));E.remove((2,p));E|=set(zip(range(p+1,p+q-1,2),range(p+2,p+q,2)))
    for mode in ['alternating_types','all_k5']:save(f'63_{q}_mixed_{mode}',g.construct(p,q,E,mode,701+len(rows)))

def exact(E,n,maxsize=None):
    es=sorted(E);idx={e:i for i,e in enumerate(es)};cliques=[]
    for k in range(2,min(n,maxsize or n)+1):
        for B in combinations(range(n),k):
            ee=set(combinations(B,2))
            if ee<=E:cliques.append((sum(1<<idx[e] for e in ee),B))
    @lru_cache(None)
    def opt(mask):
        if not mask:return ()
        bit=mask&-mask
        return min(((B,)+opt(mask^cm) for cm,B in cliques if cm&bit and cm&mask==cm),key=len)
    return list(map(list,opt((1<<len(es))-1)))
for a in range(3):
    for b in range(5):
        p=2;q=5;z=p;outside=range(p+1,p+q);E=set(combinations(range(p),2))|{(v,x) for v in range(p) for x in outside}|{(v,z) for v in range(a)}|{(z,x) for x in list(outside)[:b]}
        Bs=exact(E,p+q);Bs3=exact(E,p+q,3)
        assert (len(E)-len(Bs3))//2==1+min(a,b)
        assert len(Bs3)-len(Bs)==min(b,max(0,a-b))
        save(f'exceptional_p2_q5_a{a}_b{b}',{'kind':'exceptional','p':p,'q':q,'a':a,'b':b,'graph_edges':sorted(E),'blocks':Bs,'triangle_blocks':Bs3})
(R/'GENERATION_RESULTS.json').write_text(json.dumps({'status':'PASS_GENERATED_AND_CHECKED','cases':rows,'case_count':len(rows),'scope':'18 local boundary/adversarial cases and15 exceptional cases; finite certificates only.'},indent=2)+'\n',encoding='utf-8')
print('Generated',len(rows),'certificates')
