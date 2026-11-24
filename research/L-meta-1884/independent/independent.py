"""Self-contained independent reconstruction + exhaustive replay of L-meta-1884 numerical bound.
Run python3 independent.py --all for compilation, base checks, the 17 U2 and 18 physical cases.
"""
from pathlib import Path
from itertools import combinations,permutations,product
from functools import cache
import argparse,json,subprocess,tempfile,sys
B=Path(__file__).resolve().parent
# Verbatim endpoint ordering of all conjuncts from the original swarm statement.
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
SMALL=[(3,1),(7,2),(15,4),(45,3),(51,3),(31,7),(47,5),(55,5),(63,8),(111,7),(119,6),(189,8),(250,5),(127,9),(191,11),(251,8)]
MODES=[(1018,'delmask5'),(1020,'delmask3'),(1022,'deleted'),(1023,'petersen')]
@cache
def truth(keep):
    V=[i for i in range(10) if keep>>i&1];E=[(V.index(a),V.index(b)) for a,b in EDGES if a in V and b in V]
    return len(V),tuple(int(any((x>>a)&(x>>b)&1 for a,b in E)) for x in range(1<<len(V)))
@cache
def canonical(n,edges):
    V=sorted({i for e in edges for i in e});deg={i:sum(i in e for e in edges) for i in V};bydeg={}
    for i in V:bydeg.setdefault(deg[i],[]).append(i)
    E=set(edges);best=None
    for groups in product(*(permutations(bydeg[d]) for d in sorted(bydeg))):
        vs=sum(groups,());code=tuple(tuple(sorted((a,b))) in E for a,b in combinations(vs,2));
        if best is None or code<best:best=code
    return len(V),best
@cache
def graph(n,values):
    sing=tuple(i for i in range(n) if values[1<<i]);edges=tuple((a,b) for a,b in combinations(range(n),2) if a not in sing and b not in sing and values[(1<<a)|(1<<b)])
    for x,z in enumerate(values):
        assert z==(any(x>>i&1 for i in sing) or any(x>>a&x>>b&1 for a,b in edges))
    return sing,edges
TABLE={}
for m,c in SMALL+[(1018,12),(1020,13),(1022,15)]:
    n,t=truth(m);s,e=graph(n,t);assert not s;TABLE[canonical(n,e)]=(m,c)

def verify_tables():
    for mask,name in MODES:
        n,t=truth(mask);src=B/f'snapshot-{name}.txt';rows=[];seen=set()
        for line in src.read_text().splitlines():
            pm,val,lb=map(int,line.split());assert pm>0 and pm<1<<n and not val&~pm and (pm,val) not in seen;seen.add((pm,val))
            # With a fixed mask, increasing full input row number corresponds to compact numeric order on the free inputs.
            u=tuple(t[x] for x in range(1<<n) if x&pm==val);nn=n-pm.bit_count();s,e=graph(nn,u)
            if e:g,c=TABLE[canonical(nn,e)];assert g.bit_count()<n;cost=c+len(s)
            else:cost=max(0,len(s)-1)
            assert cost>=lb,(mask,pm,val,lb,cost);rows.append((pm,val,lb))
        print(f'{src.name}: verified {len(rows)} exact cofactor truth tables and lower bound dependencies.',flush=True)
        if mask==1023:
            act=[tuple(map(int,l.split())) for l in (B/'snapshot-physical.txt').read_text().splitlines()]
            assert act==[(pm,val,16 if pm.bit_count()==1 and val==0 else lb) for pm,val,lb in rows]
    # The physical marked-input symmetry after deleting any vertex has exactly two pair orbits.
    E={tuple(sorted(e)) for e in EDGES};V=list(combinations(range(5),2));K={(i,j) for i,j in combinations(range(10),2) if set(V[i]).isdisjoint(V[j])}
    def iso(p):
        i=len(p)
        if i==10:return p
        for v in range(10):
            if v not in p and all(((a,i) in K)==(tuple(sorted((p[a],v))) in E) for a in range(i)):
                q=iso(p+[v]);
                if q:return q
    z=iso([]);assert z is not None
    orbs={1:set(),2:set()};root={1:set(),2:set()}
    for p in permutations(range(5)):
        new=[0]*10
        for i,(a,b) in enumerate(V):new[z[i]]=z[V.index(tuple(sorted((p[a],p[b]))))]
        assert {tuple(sorted((new[a],new[b]))) for a,b in E}==E
        for j in (1,2):orbs[j].add((new[0],new[j]));root[j].add(tuple(sorted((new[0],new[j]))))
    assert {len(orbs[j]) for j in orbs}=={30,60} and len(orbs[1]|orbs[2])==90
    assert {len(root[j]) for j in root}=={15,30} and len(root[1]|root[2])==45
    print('120 explicit Petersen relabelings cover 45 unordered and 90 ordered distinct input pairs.',flush=True)

def run_cmd(args,ans,mask=None,dual=None):
    print(' '.join(map(str,args)),flush=True);out=subprocess.check_output(list(map(str,args)),text=True);print(out,flush=True)
    first,*rest=out.splitlines();assert 'result='+ans in first
    if mask is not None and dual is not None and ans=='SAT':
        n,t=truth(mask)
        gates=[tuple(map(int,l.split())) for l in rest]
        for r,z in enumerate(t):
            regs=[r>>i&1 for i in range(n)]
            for a,b,sa,sb,op,_ in gates:
                assert not sa or a==dual;assert not sb or b==dual
                x=regs[a]^sa;y=regs[b]^sb;regs.append(x|y if op else x&y)
            assert regs[-1]==z
        print(f'Physical witness agreed on all {len(t)} truth rows.',flush=True)

def run_all():
    with tempfile.TemporaryDirectory() as temp:
        root=Path(temp)
        for source in ('replay','physical'):
            subprocess.run(['c++','-std=c++17','-O3',str(B/(source+'.cpp')),'-o',str(root/source)],check=True)
        for m,c in SMALL:
            for k,ans in ((c-1,'UNSAT'),(c,'SAT')):run_cmd([root/'replay',m,k,'-',0],ans)
        for m,k,name,ans in ((1018,11,'delmask5','UNSAT'),(1018,12,'delmask5','SAT'),(1020,12,'delmask3','UNSAT'),(1022,14,'deleted','UNSAT'),(1023,17,'petersen','UNSAT')):
            run_cmd([root/'replay',m,k,B/f'snapshot-{name}.txt',1],ans)
        def phy(m,k,d,p,ans):run_cmd([root/'physical',m,k,d,p,12,1,1300000],ans,m,d)
        for m,c in [(31,7),(189,8)]:phy(m,c-1,0,'-','UNSAT');phy(m,c,0,'-','SAT')
        phy(1018,12,0,B/'snapshot-delmask5.txt','SAT')
        for d in (0,1):phy(1022,15,d,B/'snapshot-deleted.txt','UNSAT')
        phy(1023,18,0,B/'snapshot-physical.txt','UNSAT')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--all',action='store_true');args=p.parse_args();verify_tables()
    if args.all:run_all()
