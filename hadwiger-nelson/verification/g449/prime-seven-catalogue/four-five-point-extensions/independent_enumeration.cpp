// Independent exact replay: spanning stars/paths and two-pair joins.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <span>
#include <vector>
using U=std::uint64_t;
using P=std::array<int,2>;
using T=std::array<int,3>;
using Q=std::array<int,4>;
using Row=std::array<int,5>;
int n,k;
std::vector<int> deg;
std::vector<std::vector<int>> nb;
std::vector<std::array<unsigned,64>> lists;
using PM=std::map<U,std::vector<P>>;
std::set<Row> found;

bool E(int a,int b){return std::binary_search(nb[a].begin(),nb[a].end(),b);}
template<class S> bool admissible(S const&s){
    for(int a:s){
        int d=deg[a];
        for(int b:s)if(E(a,b))d++;
        if(d<5)return false;
    }
    return true;
}
bool independent_from(std::span<const int>a,std::span<const int>b){
    for(int i:a)for(int j:b)if(i==j||E(i,j))return false;
    return true;
}
// Fixed-order exhaustive assignments, unlike the first replay's
// dynamic minimum-list branching and destructive candidate masks.
bool brute(std::span<const int> s,int b,int i=0,Q c={}){
    if(i==int(s.size()))return true;
    for(int v=0;v<5;v++)if((lists[s[i]][b]>>v)&1){
        bool ok=true;
        for(int j=0;j<i;j++)if(c[j]==v && E(s[i],s[j])){ok=false;break;}
        if(ok){c[i]=v;if(brute(s,b,i+1,c))return true;}
    }
    return false;
}
U bank(std::span<const int>s){
    U a=0;
    for(int b=0;b<k;b++)if(brute(s,b))a|=U{1}<<b;
    return a;
}
void emit(int shape,Q q){
    std::sort(q.begin(),q.end());
    assert(std::adjacent_find(q.begin(),q.end())==q.end());
    assert(found.insert({shape,q[0],q[1],q[2],q[3]}).second);
}
int main(int argc,char**argv){
    assert(argc==3);
    std::ifstream in(argv[1]);
    int m;
    assert(in>>n>>k>>m);
    assert(0<k && k<64);
    deg.resize(n); lists.resize(n); nb.resize(n);
    for(int i=0;i<n;i++){
        assert(in>>deg[i]);
        for(int b=0;b<k;b++){assert(in>>lists[i][b]);assert(lists[i][b]<32);}
    }
    for(int i=0;i<m;i++){
        int a,b;assert(in>>a>>b);
        nb[a].push_back(b);nb[b].push_back(a);
    }
    for(auto &x:nb)std::sort(x.begin(),x.end());
    std::set<Q> con;
    auto add4=[&](Q s){
        std::sort(s.begin(),s.end());
        if(std::adjacent_find(s.begin(),s.end())==s.end() && admissible(s))con.insert(s);
    };
    std::set<T> tri;
    // Every connected four-set has either a spanning star or a spanning path.
    for(int a=0;a<n;a++)for(int b:nb[a]){
        for(int c:nb[a])if(c>b){
            T t={a,b,c};
            std::sort(t.begin(),t.end());
            if(admissible(t))tri.insert(t);
            for(int d:nb[a])if(d>c)add4({a,b,c,d});
        }
        if(b>a)for(int c:nb[a])if(c!=b)for(int d:nb[b])if(d!=a&&d!=c)
            add4({c,a,b,d});
    }
    assert(con.size()==115395 && tri.size()==13188);
    for(auto const&q:con)if(!bank(q))emit(4,q);
    std::cout<<"Spanning stars and paths: "<<con.size()<<" connected quartets.\n";

    std::vector<int> highs;
    std::vector<U> highMask(n);
    for(int i=0;i<n;i++)if(deg[i]>=5){
        highs.push_back(i);
        highMask[i]=bank(std::array<int,1>{i});
    }
    PM nonedge, edge;
    for(int a:highs)for(int b:highs)if(a<b && !E(a,b))
        nonedge[highMask[a]&highMask[b]].push_back({a,b});
    for(int a=0;a<n;a++)if(deg[a]>=4)for(int b:nb[a])if(a<b&&deg[b]>=4){
        P p={a,b};
        edge[bank(p)].push_back(p);
    }
    // Four singletons: pair the smallest two and the largest two.
    for(auto const &[x,low]:nonedge)for(auto const &[y,high]:nonedge)if(!(x&y))
        for(auto const&a:low)for(auto const&b:high)
            if(a[1]<b[0] && independent_from(a,b))emit(0,{a[0],a[1],b[0],b[1]});
    // One edge and two mutually nonadjacent singletons.
    for(auto const &[x,edges]:edge)for(auto const &[y,iso]:nonedge)if(!(x&y))
        for(auto const&a:edges)for(auto const&b:iso)
            if(independent_from(a,b))emit(1,{a[0],a[1],b[0],b[1]});
    for(auto const &[x,edges1]:edge)for(auto const &[y,edges2]:edge)if(!(x&y))
        for(auto const&a:edges1)for(auto const&b:edges2)
            if(a[0]<b[0] && independent_from(a,b))emit(2,{a[0],a[1],b[0],b[1]});
    for(auto const&a:tri){
        U x=bank(a);
        for(int b:highs)if(!(x&highMask[b]) && independent_from(a,std::array<int,1>{b}))
            emit(3,{a[0],a[1],a[2],b});
    }
    std::set<Row> expected;
    std::ifstream rows(argv[2]);
    Row r{};
    while(rows>>r[0]){
        assert(rows>>r[1]>>r[2]>>r[3]>>r[4]);
        assert(expected.insert(r).second);
    }
    assert(found==expected && found.size()==8629);
    std::cout<<"Independent pair-mask joins: exactly "<<found.size()
             <<" residual quartets, agreeing row for row.\n";
}
