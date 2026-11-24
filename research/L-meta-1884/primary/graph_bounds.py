"""Exact U2 costs for induced subgraphs, up to isomorphism; emit pin constraints for the larger search."""
import functools,itertools,json,subprocess,sys
from pathlib import Path
b=Path(__file__).resolve().parent
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
adj=[sum(1<<(u^v^i) for u,v in edges if i in (u,v)) for i in range(10)]
@functools.cache
def core(s):
 return sum(1<<i for i in range(10) if s>>i&1 and s&adj[i])
@functools.cache
def canon(s):
 vs=[i for i in range(10) if s>>i&1]
 parts={}
 for i in vs:parts.setdefault((s&adj[i]).bit_count(),[]).append(i)
 # Stable degree-class order, lexicographically minimal adjacency bits.
 if len(vs)>8:return ('large',s)
 return len(vs),min((sum(((adj[i]>>j)&1)<<(p*(p-1)//2+q) for p,i in enumerate(order) for q,j in enumerate(order[:p])) for perm in itertools.product(*(itertools.permutations(parts[k]) for k in sorted(parts))) for order in [sum(perm,())]),default=0)
def upper(s):
 e=sum((s>>i)&(s>>j)&1 for i,j in edges)
 cover=min(c.bit_count() for c in range(1024) if not c&~s and not core(s^c))
 return max(0,e+cover-1)
def costs(binary=None, save=None):
 binary=Path(binary) if binary else b/'frontier2'
 save=Path(save) if save else b/'small-costs.json'
 out={}
 for s in sorted(set(core(m) for m in range(1024)),key=int.bit_count):
  n=s.bit_count()
  if n>7 or n==0:continue
  tag=str(canon(s))
  if tag in out:continue
  ub=upper(s); evidence=[]
  for k in range(ub-1,n-2,-1):
   log=subprocess.check_output([str(binary),str(k),'delmask'+str(1023^s),'0'],stderr=subprocess.DEVNULL,text=True)
   evidence.append(log.splitlines()[0])
   if 'found 0 ' in log.splitlines()[0]:break
   ub=k
  out[tag]={'mask':s,'cost':ub,'runs':evidence}
  print(n,s,ub,flush=True)
  save.write_text(json.dumps(out,indent=2)+'\n')
def constraints(mode,limit,cost_file=None,folder=None):
 folder=Path(folder) if folder else b
 data=json.loads((Path(cost_file) if cost_file else b/'small-costs.json').read_text());keep=1023 if mode=='petersen' else 1022 if mode=='deleted' else 1023^int(mode.removeprefix('delmask'))
 vs=[i for i in range(10) if keep>>i&1]; n=len(vs); out=[]
 for pins in range(1,min(limit,n-1)+1):
  for sel in itertools.combinations(range(n),pins):
   raw=sum(1<<vs[i] for i in sel);fix=sum(1<<i for i in sel)
   for ones in range(1<<pins):
    on=sum(1<<vs[i] for j,i in enumerate(sel) if ones>>j&1)
    if core(on):continue
    free=keep^raw; sing=free&functools.reduce(int.__or__,(adj[i] for i in vs if on>>i&1),0)
    g=core(free&~sing)
    if not g and not sing:continue
    size=g.bit_count(); gc=0
    if g:
     if size<=7:gc=data[str(canon(g))]['cost']
     elif size==8:gc=13 if core(1023 ^ g) else 12
     elif size==9:gc=15
     else:raise ValueError
     bound=gc+sing.bit_count()
    else:bound=sing.bit_count()-1
    val=sum(1<<i for j,i in enumerate(sel) if ones>>j&1)
    out.append((fix,val,bound))
 with open(folder/f'pins-{mode}.txt','w') as f:
  for line in out:print(*line,file=f)
 print(mode, len(out))
if __name__=='__main__':
 if sys.argv[1]=='costs':costs()
 else:constraints(sys.argv[1],int(sys.argv[2]))
