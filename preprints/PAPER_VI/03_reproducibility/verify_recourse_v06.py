"""Read-only replay of all physical recourse states; no generator imports."""
from pathlib import Path
from collections import Counter
import gzip,json,hashlib
from verify_v06 import partition,pairs
R=Path(__file__).resolve().parent;f=R/'RECOURSE_TWO_EDGES.json.gz';d=json.loads(gzip.decompress(f.read_bytes()));p,q=d['p'],d['q'];E=set(map(tuple,d['graph_edges']));states=[];liftings=[]
outer={e for e in E if e[0]>=p};m=len(outer)
assert pairs(range(p))|{(a,x) for a in range(p) for x in range(p,p+q)}<=E
actual_h=max(Counter(v for e in outer for v in e).values(),default=0)
assert actual_h==d['h']
for raw in d['states']:
    Bs={frozenset(B) for B in raw};partition(p+q,d['graph_edges'],raw)
    assert len(Bs)==len(raw)==p*q-p*(p-1)//2-2*m
    assert all((sum(v<p for v in B),sum(v>=p for v in B)) in [(3,2),(2,1),(1,1)] for B in Bs)
    L={tuple(sorted(v for v in B if v>=p)):B for B in Bs if len(B)==5}
    assert set(L)==outer and len(L)==m
    loads=Counter(v for B in L.values() for v in B if v<p)
    assert max(loads.values(),default=0)<=7*d['h']
    liftings.append(L);states.append(Bs)
assert p>=63*d['h'] and 2*p-1<=q<=2*p+1
k=sum(liftings[0][e]!=liftings[1][e] for e in outer);assert k==d['changed_liftings']==1
safe={B for B in states[0] if len(B)==3 and not any(pairs(B)&pairs(Q) for Q in liftings[1].values())}
assert safe<=states[1] and len(safe)==d['safe_terminal_triangles_retained']
assert frozenset(d['protected_lifting']) in states[0]&states[1]
lost=len(states[0]-states[1]);sd=len(states[0]^states[1]);terminal=len(states[1]^states[2])
assert lost==d['old_lost']<=34*k and sd==d['symmetric_difference']<=68*k
assert liftings[1]==liftings[2] and terminal==d['terminal_difference']<=18
assert len(states)-1==d['path_steps']<=p*(p-1)//2-2*m
assert d['path_bound']==p*(p-1)//2-2*m and d['step_bound']==884
assert all(len(a^b)<=884 for a,b in zip(states,states[1:]))
out={'status':'PASS_INDEPENDENT_PHYSICAL_RECOURSE','states':len(states),'exterior_edges':m,'changed_liftings':k,'retained_safe_triangles':len(safe),'lost':lost,'symmetric_difference':sd,'terminal_difference':terminal,'path_steps':len(states)-1,'path_bound':p*(p-1)//2-2*m,'certificate_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'scope':'One finite two-edge recourse path, not a universal connectivity proof.'}
(R/'RECOURSE_INDEPENDENT_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out,indent=2))
