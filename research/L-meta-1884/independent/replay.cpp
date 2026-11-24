// A separate exhaustive U2 checker. Compare the exact row partitions after retiring inputs.
// Trace state is a list of live truth functions plus three-valued restrictions and numeric budgets.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using T=array<uint64_t,16>; using Key=vector<int>; const int M=24,P=8192;
struct Hash { template<class A> size_t operator()(const A& x)const{size_t h=0;for(auto v:x)h=(h+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2))^v;return h;} };
vector<T> funcs;unordered_map<T,int,Hash> ids;unordered_map<Key,uint8_t,Hash> seen;
int n,k,nrows,nt,pins,words,goal,syms;uint64_t calls,dropped,reused;
array<uint16_t,1024> rowcode[M];array<int8_t,P> constantAt[48],leftover[M];
array<uint16_t,1024> negrows;int nneg;uint8_t label[1024];uint8_t clash[1<<20];
struct Wire {int id,reg;};
struct Pin{int mask,val,lb;}; vector<Pin> checks;
int make(const T& f){auto it=ids.find(f);if(it!=ids.end())return it->second;int h=funcs.size();ids.emplace(f,h);funcs.push_back(f);return h;}
struct LUT{int8_t price,result;};LUT rule[4][4][3][3];
void init_rules(){for(int code=0;code<4;code++)for(int keep=0;keep<4;keep++)for(int a=0;a<3;a++)for(int b=0;b<3;b++){
    // Codes are 0=unknown, 1=fixed 0, 2=fixed 1. The gate tests a two-bit pattern.
    bool fa=a,fb=b;int ca=code&1,cb=code>>1;
    bool forcedFalse=(fa && a-1!=ca)||(fb && b-1!=cb);
    bool forcedTrue=fa&&fb&&!forcedFalse;int fresh=forcedFalse?1:forcedTrue?2:0;
    int kill=fa||fb; int retained=(int)(fa && (keep&1))+(int)(fb && (keep&2))+(fresh!=0);
    int saved=kill +retained-fa-fb;if(saved<0 || saved>2)abort();
    rule[code][keep][a][b]={static_cast<int8_t>(saved),static_cast<int8_t>(fresh)};
}}
bool pinOK(int d,int i,int j,int code,int keep,bool neg){
    auto &r=rule[code][keep];auto &a=constantAt[i],&b=constantAt[j],&out=constantAt[n+d];
    for(int q=0;q<pins;q++){auto x=r[a[q]][b[q]];int rem=leftover[d][q]-x.price;if(rem<0)return false;
        leftover[d+1][q]=rem;out[q]=neg && x.result?3-x.result:x.result;}
    return true;
}
bool rec(const vector<Wire>& live,int d){
    calls++;int L=live.size(),remaining=k-d;
    for(auto w:live)if(w.id==goal)return true;
    if(L<2||remaining<L-1||!remaining)return false;
    Key key;for(auto w:live)key.push_back(w.id);sort(key.begin(),key.end());
    if(auto it=seen.find(key);it!=seen.end()&&it->second>=remaining){reused++;return false;}
    auto &r=rowcode[d];int ct=1<<L;fill(clash,clash+ct,0);
    for(int x=0;x<nrows;x++)clash[r[x]]=1+label[x];
    // Record the Boolean patterns of every oppositely labelled pair at Hamming distance 1 or 2.
    // Distances >2 cannot collide after a gate retires at most two coordinates.
    unsigned diffZero[M]={},diffOne[M]={};uint8_t diag[M][M]={};
    const unsigned full=ct-1;
    for(int ix=0;ix<nneg;ix++){
        int u=r[negrows[ix]];
        for(int i=0;i<L;i++){
            int w=u^(1<<i);
            if(clash[w]==2){diffOne[i]|=u;diffZero[i]|=(~u)&full;}
            for(int j=i+1;j<L;j++)if(clash[w^(1<<j)]==2)diag[i][j]|=1<<(((u>>i)^(u>>j))&1);
        }
    }
    for(int keep=0;keep<4;keep++){
        int nextL=L-1+__builtin_popcount((unsigned)keep);
        if(remaining-1<nextL-1)continue;
        for(int i=0;i<L;i++)for(int j=i+1;j<L;j++){
            // Root pair orbits for the Petersen graph. The exact ten-bit targets are separately checked.
            if(!d&&syms&&n==10&&(i!=0||(j!=1&&j!=2)))continue;
            auto wa=live[i],wb=live[j];
            for(int code=0;code<4;code++){
                int a=code&1,b=code>>1;bool keepA=keep&1,keepB=keep&2;
                if(!keepA && ((b?diffZero[i]:diffOne[i])&(1u<<j)))continue;
                if(!keepB && ((a?diffZero[j]:diffOne[j])&(1u<<i)))continue;
                if(!keepA&&!keepB && (diag[i][j]&(1u<<(1^a^b))))continue;
                // All function representatives take value zero at the all-zero assignment.
                bool inverse=(code==0);
                if(!pinOK(d,wa.reg,wb.reg,code,keep,inverse)){dropped++;continue;}
                T f{};const T& x=funcs[wa.id];const T& y=funcs[wb.id];
                for(int q=0;q<words;q++){auto lhs=a?x[q]:~x[q],rhs=b?y[q]:~y[q];f[q]=(lhs&rhs)^(inverse?UINT64_MAX:0);}
                if(nrows<64)f[0]&=(uint64_t(1)<<nrows)-1;
                if(f==T{})continue;
                int id=make(f);if(any_of(live.begin(),live.end(),[&](auto w){return w.id==id;}))continue;
                vector<Wire> next;for(int s=0;s<L;s++)if((s!=i||keepA)&&(s!=j||keepB))next.push_back(live[s]);
                int out=next.size();next.push_back({id,n+d});
                for(int row=0;row<nrows;row++){
                    int source=r[row];int pat=((source>>i)&1)+2*((source>>j)&1);int value=(pat==code)^inverse;
                    if(!keepB){int m=(1<<j)-1;source=(source&m)|((source>>1)&~m);}
                    if(!keepA){int m=(1<<i)-1;source=(source&m)|((source>>1)&~m);}
                    rowcode[d+1][row]=source|(value<<out);
                }
                if(rec(next,d+1))return true;
            }
        }
    }
    if(seen.size()<900000){auto &v=seen[key];v=max<int>(v,remaining);}return false;
}
int main(int ac,char**av){if(ac<4)return 2;int keep=stoi(av[1]);k=stoi(av[2]);syms=ac>4?stoi(av[4]):1;
    int adj[10]={50,69,138,276,521,385,770,548,104,208};vector<int> vs;
    for(int i=0;i<10;i++)if(keep>>i&1)vs.push_back(i);n=vs.size();nrows=1<<n;words=(nrows+63)/64;
    init_rules();T f{};vector<Wire> live;
    for(int r=0;r<nrows;r++){rowcode[0][r]=r;int orig=0;for(int i=0;i<n;i++)if(r>>i&1)orig|=1<<vs[i];
        bool edge=false;for(auto i:vs)if((orig>>i&1)&&(adj[i]&orig))edge=true;label[r]=edge;
        if(edge)f[r/64]|=uint64_t(1)<<(r%64);else negrows[nneg++]=r;}
    goal=make(f);for(int i=0;i<n;i++){T x{};for(int r=0;r<nrows;r++)if(r>>i&1)x[r/64]|=uint64_t(1)<<(r%64);live.push_back({make(x),i});}
    if(string(av[3])!="-"){ifstream fin(av[3]);if(!fin)return 3;Pin p;while(fin>>p.mask>>p.val>>p.lb){
        if(p.mask>=nrows||p.val&~p.mask||p.lb<=0)return 4;checks.push_back(p);}}
    sort(checks.begin(),checks.end(),[](auto a,auto b){return a.lb+__builtin_popcount((unsigned)a.mask)>b.lb+__builtin_popcount((unsigned)b.mask);});
    for(auto p:checks){int cap=k-p.lb-__builtin_popcount((unsigned)p.mask);if(cap<0){cout<<"mask="<<keep<<" k="<<k<<" pin-mask="<<p.mask<<" pin-bits="<<p.val<<" pin-lower="<<p.lb<<" result=UNSAT by root pin only\n";return 0;}if(pins>=P)return 5;
        for(int i=0;i<n;i++)if(p.mask>>i&1)constantAt[i][pins]=1+(p.val>>i&1);leftover[0][pins++]=cap;}
    auto tic=chrono::steady_clock::now();bool found=rec(live,0);
    cout<<"mask="<<keep<<" n="<<n<<" k="<<k<<" pins="<<pins<<" result="<<(found?"SAT":"UNSAT")<<" calls="<<calls<<" pin_prunes="<<dropped<<" cache_hits="<<reused<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-tic).count()<<"\n";
}
