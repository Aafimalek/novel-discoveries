// Independent replay: sorted connected subsets with frontier growth,
// fixed-order brute-force list coloring, and direct mask joins.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <span>
#include <vector>
using U=std::uint64_t;
using V=std::array<int,5>;
using R=std::array<int,6>;
struct Group{U mask;std::vector<V> points;};
int n,k;
std::vector<int>D;
std::vector<std::array<unsigned,64>> lists;
std::vector<std::vector<int>> N;
std::vector<U> matrix;
int W;
std::array<std::map<U,std::vector<V>>,5> pending;
std::array<std::vector<Group>,5> bankGroups;
std::set<R> want;
std::array<std::uint64_t,7> nr;
bool E(int a,int b){return (matrix[U(a)*W+b/64]>>(b%64))&1;}
bool admissible(V const&v,int m,int remaining){
    for(int i=0;i<m;i++){
        int d=D[v[i]];
        for(int j=0;j<m;j++)d+=E(v[i],v[j]);
        if(d+remaining<5)return false;
    }
    return true;
}
bool brute(V const&v,int m,int b,int i=0,V c={}){
    if(i==m)return true;
    for(int q=0;q<5;q++)if((lists[v[i]][b]>>q)&1){
        bool ok=true;
        for(int j=0;j<i;j++)if(c[j]==q && E(v[i],v[j])){ok=false;break;}
        if(ok){ c[i]=q; if(brute(v,m,b,i+1,c))return true; }
    }
    return false;
}
U mask(V const&v,int m){
    U r=0;
    for(int b=0;b<k;b++)if(brute(v,m,b))r|=U{1}<<b;
    return r;
}
void emit(int shape,V s){
    std::sort(s.begin(),s.end());
    assert(std::adjacent_find(s.begin(),s.end())==s.end());
    R r={shape,s[0],s[1],s[2],s[3],s[4]};
    assert(want.erase(r)==1);
    nr[shape]++;
}
void traverse(){
    std::array<std::uint64_t,6> nv{};
    for(int v=0;v<n;v++){
        std::set<V> seen{{{v,-1,-1,-1,-1}}};
        for(int m=1;m<=5;m++){
            std::set<V> next;
            nv[m]+=seen.size();
            for(auto const&a:seen){
                if(m==5){
                    int b=0;
                    for(;b<k;b++)if(brute(a,m,b))break;
                    if(b==k)emit(6,a);
                }else{
                    if(admissible(a,m,0))pending[m][mask(a,m)].push_back(a);
                    for(int i=0;i<m;i++)for(int x:N[a[i]]){
                        if(x<=v || std::binary_search(a.begin(),a.begin()+m,x))continue;
                        V q=a; q[m]=x;
                        for(int j=m;j>0&&q[j-1]>q[j];j--)std::swap(q[j-1],q[j]);
                        if(admissible(q,m+1,4-m))next.insert(q);
                    }
                }
            }
            seen.swap(next);
        }
    }
    assert((nv==std::array<std::uint64_t,6>{0,7056,33908,363510,1133020,1119839}));
    std::cout<<"Independent connected frontier counts:";
    for(int i=1;i<=5;i++)std::cout<<" "<<nv[i];
    std::cout<<std::endl;
    for(int m=1;m<=4;m++){
        for(auto &p:pending[m])bankGroups[m].push_back({p.first,std::move(p.second)});
        pending[m].clear();
    }
}
void expand(int shape,std::span<const int> sizes, std::array<Group const*,5> const& g,
            int depth=0,int off=0,int floor=0,V buf={}){
    if(depth==int(sizes.size())){emit(shape,buf);return;}
    Group const &h=*g[depth];
    for(int idx=floor;idx<int(h.points.size());idx++){
        auto const &a=h.points[idx];
        bool ok=true;
        for(int i=0;i<sizes[depth]&&ok;i++)for(int j=0;j<off;j++)
            if(a[i]==buf[j]||E(a[i],buf[j])){ok=false;break;}
        if(!ok)continue;
        for(int i=0;i<sizes[depth];i++)buf[off+i]=a[i];
        expand(shape,sizes,g,depth+1,off+sizes[depth],
               depth+1<int(sizes.size()) && g[depth+1]==g[depth]?idx+1:0,buf);
    }
}
void groupJoin(int shape,std::span<const int>sz,int depth,int start,U curr,
               std::array<Group const*,5> &g){
    auto const&G=bankGroups[sz[depth]];
    if(depth+1==int(sz.size())){
        for(int j=start;j<int(G.size());j++)if(!(curr&G[j].mask)){
            g[depth]=&G[j];
            expand(shape,sz,g);
        }
        return;
    }
    for(int j=start;j<int(G.size());j++){
        g[depth]=&G[j];
        groupJoin(shape,sz,depth+1,sz[depth+1]==sz[depth]?j:0,curr&G[j].mask,g);
    }
}
int main(int argc,char**argv){
    assert(argc==3);
    std::ifstream s(argv[1]);
    int m;assert(s>>n>>k>>m);
    assert(n==7056 && k==37 && m==33908);
    W=(n+63)/64;
    D.resize(n); lists.resize(n); N.resize(n);matrix.resize(U(n)*W);
    for(int i=0;i<n;i++){
        assert(s>>D[i]&&D[i]>=2);
        for(int j=0;j<k;j++)assert(s>>lists[i][j]&&lists[i][j]<32);
    }
    for(int i=0;i<m;i++){
        int a,b;assert(s>>a>>b&&0<=a&&a<b&&b<n&&!E(a,b));
        matrix[U(a)*W+b/64]|=U{1}<<(b%64);
        matrix[U(b)*W+a/64]|=U{1}<<(a%64);
        N[a].push_back(b);N[b].push_back(a);
    }
    std::ifstream in(argv[2]);
    R r;
    while(in>>r[0]){
        for(int i=1;i<6;i++)assert(in>>r[i]);
        assert(want.insert(r).second);
    }
    assert(want.size()==138009);
    traverse();
    std::array<std::vector<int>,6> const P{{{1,1,1,1,1},{1,1,1,2},{1,2,2},{1,1,3},{2,3},{1,4}}};
    for(int shape=0;shape<6;shape++){
        std::array<Group const*,5> g{};
        groupJoin(shape,P[shape],0,0,(U{1}<<k)-1,g);
        std::cout<<"Direct join shape "<<shape<<" residual "<<nr[shape]<<std::endl;
    }
    assert(want.empty());
    std::cout<<"Exact agreement of all 138009 residual quintets, including "
             <<nr[6]<<" connected ones."<<std::endl;
}
