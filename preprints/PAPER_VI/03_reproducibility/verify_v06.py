"""Independent literal verifier: no generator imports, Lean or solver."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import gzip,json,hashlib

def pairs(B): return {tuple(sorted(e)) for e in combinations(B,2)}
def partition(n,E,Bs):
    assert len(E)==len(set(map(tuple,E))), 'duplicate_graph_edge'
    E=set(map(tuple,E));counts=Counter()
    for B in Bs:
        assert len(B)>=2 and len(set(B))==len(B) and all(0<=v<n for v in B), 'block_domain'
        assert pairs(B)<=E, 'nonclique'
        counts.update(pairs(B))
    assert set(counts)==E, 'missing_coverage'
    assert all(c==1 for c in counts.values()), 'double_coverage'
    return E

def verify(d):
    p,q=d['p'],d['q'];E=partition(p+q,d['graph_edges'],d['blocks'])
    S=pairs(range(p))|{(a,x) for a in range(p) for x in range(p,p+q)}
    h=max(Counter(v for e in E^S for v in e).values(),default=0)
    u=sum(b<p for a,b in E);m=sum(a>=p for a,b in E);s=len(E)-u-m
    if d.get('kind')=='exceptional':
        a,b=d['a'],d['b'];Phi=p*(q-1)-p*(p-1)//2+a-2*b
        assert len(d['blocks'])==Phi+max(0,2*b-a,3*b-2*a)
        vertices=range(p+q);z=p;R=set(range(p+1,p+q));values=[]
        for ca,cb in [(0,0),(-1,2),(-2,3)]:
            weights={e:(-1 if e[1]<p else -2 if e[0]>=p else 1)+(ca if z in e and any(v<p for v in e) else cb if z in e and any(v in R for v in e) else 0) for e in E}
            for size in range(2,p+q+1):
                for B in combinations(vertices,size):
                    if pairs(B)<=E: assert sum(weights[e] for e in pairs(B))<=1,'invalid_dual'
            values.append(sum(weights.values()))
        assert max(values)==len(d['blocks']),'primal_dual_gap'
        partition(p+q,d['graph_edges'],d['triangle_blocks'])
        assert max(map(len,d['triangle_blocks']),default=0)<=3
        nu=(len(E)-len(d['triangle_blocks']))//2
        assert len(E)-len(d['triangle_blocks'])==2*nu and nu==p*(p-1)//2+min(a,b)
        cover={e:int(e[1]<p or (z in e and (any(v<p for v in e) if a<=b else any(v in R for v in e)))) for e in E}
        for B in combinations(vertices,3):
            if pairs(B)<=E:assert sum(cover[e] for e in pairs(B))>=1,'invalid_triangle_dual'
        assert sum(cover.values())==nu,'triangle_primal_dual_gap'
        assert len(d['triangle_blocks'])-len(d['blocks'])==min(b,max(0,a-b))
        return {'kind':'exceptional','p':p,'q':q,'a':a,'b':b,'cp':len(d['blocks']),'duals':values}
    tri=d['mode']=='triangles'
    assert len(d['blocks'])==s-u-(m if tri else 2*m),'wrong_objective'
    assert p==((p+q+1)//3)
    if d['mode'] in ['alternating_types','random_types','all_k5']:assert p>=63*h,'outside_theorem_C'
    else:assert p>=18*h+1 or (q==2*p and p>=18*h),'outside_theorem_A_B'
    types=Counter((sum(v<p for v in B),sum(v>=p for v in B)) for B in d['blocks'])
    if tri:
        assert max(map(len,d['blocks']),default=0)<=3
        assert all(a*(a-1)//2+(3-a)*(2-a)//2>=1 for a in range(4))
    else:
        assert all(1-a*b+a*(a-1)//2+b*(b-1)==0 for a,b in types),'positive_slack'
        # All possible host clique types, including impossible ones, satisfy the
        # signed-dual inequality. This avoids enumerating exponentially many cliques.
        assert all(1-aa*bb+aa*(aa-1)//2+bb*(bb-1)>=0 for aa in range(p+1) for bb in range(q+1) if aa+bb>=2),'invalid_local_dual'
    for key,size in d['outside_type_assignment'].items():
        x,y=map(int,key.split(','));occ=[B for B in d['blocks'] if x in B and y in B]
        assert len(occ)==1 and len(occ[0])==size,'prescription'
    return {'kind':'local','p':p,'q':q,'h':h,'u':u,'m':m,'s':s,'blocks':len(d['blocks']),'edges':len(E),'mode':d['mode']}

if __name__=='__main__':
    root=Path(__file__).resolve().parent;rows=[]
    for p in sorted((root/'certificates').glob('*.json.gz')):
        row=verify(json.loads(gzip.decompress(p.read_bytes())));row['certificate']=p.name;row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest();rows.append(row)
    result={'status':'PASS_INDEPENDENT_LITERAL_CHECKS','cases':rows,'count':len(rows),'scope':'Finite regression certificates only; no universal theorem inferred.'}
    (root/'INDEPENDENT_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],len(rows))
