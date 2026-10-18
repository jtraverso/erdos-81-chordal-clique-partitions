"""Two exterior edges, one protected K5 lifting, one changed lifting."""
from pathlib import Path
from itertools import combinations
import json,gzip,copy,hashlib
from verify_v06 import pairs,partition
R=Path(__file__).resolve().parent;p=63;q=125;O=range(p,p+q)
ext=[(p,p+1),(p+2,p+3)];E=pairs(range(p))|{(a,x) for a in range(p) for x in O}|set(ext)
def complete(cores,prefix=()):
    Bs=[frozenset(core+e) for core,e in zip(cores,ext)];used=set().union(*(pairs(B) for B in Bs))
    for B in prefix:
        assert not pairs(B)&used;Bs.append(B);used|=pairs(B)
    for a,b in combinations(range(p),2):
        if (a,b) in used:continue
        free=next(x for x in O if (a,x) not in used and (b,x) not in used)
        B=frozenset((a,b,free));Bs.append(B);used|=pairs(B)
    Bs.extend(frozenset(e) for e in sorted(E-used));partition(p+q,sorted(E),Bs)
    assert len(Bs)==p*q-p*(p-1)//2-4
    return set(Bs)
old=complete([(0,1,2),(3,4,5)]);newbig=pairs((6,7,8,p,p+1))|pairs((3,4,5,p+2,p+3))
safe={B for B in old if len(B)==3 and not pairs(B)&newbig}
new=complete([(6,7,8),(3,4,5)],sorted(safe,key=lambda B:tuple(sorted(B))))
common=frozenset((3,4,5,p+2,p+3));assert common in old&new and safe<=new
lost=len(old-new);sd=len(old^new);assert lost<=34 and sd<=68
for B in sorted(new,key=lambda B:tuple(sorted(B))):
    if len(B)!=3:continue
    a,b=sorted(v for v in B if v<p);x=next(v for v in B if v>=p)
    for y in O:
        if y!=x and frozenset((a,y)) in new and frozenset((b,y)) in new:
            target=new-{B,frozenset((a,y)),frozenset((b,y))}|{frozenset((a,b,y)),frozenset((a,x)),frozenset((b,x))};break
    else:continue
    break
else:raise AssertionError('No terminal recoloring')
partition(p+q,sorted(E),target);assert len(target)==len(new) and len(target^new)<=18
payload={'p':p,'q':q,'h':1,'graph_edges':sorted(E),'states':[[sorted(B) for B in sorted(Bs,key=lambda B:tuple(sorted(B)))] for Bs in [old,new,target]],'changed_liftings':1,'protected_lifting':sorted(common),'safe_terminal_triangles_retained':len(safe),'old_lost':lost,'symmetric_difference':sd,'terminal_difference':len(target^new),'path_steps':2,'path_bound':p*(p-1)//2-4,'step_bound':884,'scope':'A physical three-state example in the bounded-load all-K5 class, not a universal path algorithm.'}
assert max(sum(v in B for B in old if len(B)==5) for v in range(p))<=7
f=R/'RECOURSE_TWO_EDGES.json.gz';f.write_bytes(gzip.compress(json.dumps(payload).encode(),mtime=0))
negative=[]
for name,actual,bound in [('understated_symmetric_difference',sd,sd-1),('understated_lifting_load',1,0)]:
    assert not actual<=bound;negative.append({'name':name,'actual':actual,'invalid_bound':bound,'rejected':True})
(R/'RECOURSE_RESULTS.json').write_text(json.dumps({k:v for k,v in payload.items() if k not in ['graph_edges','states']}|{'status':'PASS','certificate_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'negative_controls':negative},indent=2)+'\n',encoding='utf-8')
print('Two-edge recourse PASS:',lost,sd,len(target^new),'safe',len(safe))
