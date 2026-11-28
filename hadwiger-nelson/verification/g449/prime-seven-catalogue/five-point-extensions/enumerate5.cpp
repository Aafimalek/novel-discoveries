#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>

using I=std::uint64_t;

using Five = std::array<int,5>;
struct Component { int n; Five v; };
struct Group {I mask; std::vector<Component> list;};

struct Audit {
    int n,k,W;
    I bank;
    std::vector<int>D;
    std::vector<std::array<std::uint8_t,64>> lists;
    std::vector<std::vector<int>> nb;
    std::vector<I> matrix;
    std::array<std::vector<Group>,5> groups;
    std::array<std::map<I, std::vector<Component>>,5> pending;
    std::array<std::vector<std::array<I,64>>,5> acceptByWord;
    std::array<I,7> residual{}, types{}, tested{};
    std::array<I,5> cn{};
    std::ofstream out;
    bool E(int a,int b) const { return (matrix[(I)a*W+b/64]>>(b%64))&1; }
    Audit(char* input,char* output):out(output) {
        assert(out.good());
        std::ifstream s(input);
        int m;
        assert(s>>n>>k>>m);
        assert(n>0 && 0<k && k<64);
        W=(n+63)/64; bank=(I{1}<<k)-1;
        matrix.resize(I(n)*W);
        D.resize(n); lists.resize(n); nb.resize(n);
        for(int i=0;i<n;i++){
            assert(s>>D[i] && D[i]>=2);
            for(int j=0;j<k;j++){
                int t; assert(s>>t && 0<=t && t<32); lists[i][j]=t;
            }
        }
        for(int i=0;i<m;i++){
            int a,b; assert(s>>a>>b);
            assert(a>=0 && a<b && b<n && !E(a,b));
            matrix[(I)a*W+b/64]|=I{1}<<(b%64);
            matrix[(I)b*W+a/64]|=I{1}<<(a%64);
            nb[a].push_back(b); nb[b].push_back(a);
        }
    }
    std::array<int,5> adj(Component const &C) const{
        std::array<int,5> a{};
        for(int i=0;i<C.n;i++)for(int j=i+1;j<C.n;j++)if(E(C.v[i],C.v[j])){
            a[i]|=1<<j; a[j]|=1<<i;
        }
        return a;
    }
    bool colored(std::array<int,5> const&a,Five l,int left) const{
        if(!left) return true;
        int i=-1,min=6;
        for(int j=0;j<5;j++)if((left>>j)&1){
            int t=std::popcount(unsigned(l[j]));
            if(t==0) return false;
            if(t<min){min=t;i=j;}
        }
        assert(i>=0);
        for(unsigned available=l[i];available;available&=available-1){
            Five keep=l;
            int cl = 1<<std::countr_zero(available);
            int further=(left^(1<<i));
            for(int j=0;j<5;j++)if(((further&a[i])>>j)&1)keep[j]&=~cl;
            if(colored(a,keep,further)) return true;
        }
        return false;
    }
    bool good(Component const &C,std::array<int,5> const&a,int b) const {
        Five l{};
        for(int i=0;i<C.n;i++)l[i]=lists[C.v[i]][b];
        return colored(a,l,(1<<C.n)-1);
    }
    I mask(Component const&C) const {
        auto a=adj(C);
        I s=0;
        for(int b=0;b<k;b++) if(good(C,a,b)) s|=I{1}<<b;
        return s;
    }
    void write(int shape,Five r) {
        std::sort(r.begin(),r.end());
        assert(std::adjacent_find(r.begin(),r.end())==r.end());
        out<<shape;
        for(int i:r) out<<' '<<i;
        out<<'\n';
        residual[shape]++;
    }
    bool fits(Component const &T,std::array<int,5> const&a) const{
        int remaining=5-T.n;
        for(int j=0;j<T.n;j++)
            if(D[T.v[j]]+std::popcount(unsigned(a[j]))+remaining<5) return false;
        return true;
    }
    bool isConnected(std::array<int,5> const& a,int subset) const{
        assert(subset>0);
        int seen=subset&-subset;
        for(int j=0;j<4;j++) {
            int expanded=seen;
            for(int v=0;v<5;v++) if((seen>>v)&1)expanded|=(a[v]&subset);
            if(expanded==seen)break;
            seen=expanded;
        }
        return seen==subset;
    }
    void walk(Component const&S){
        assert(1<=S.n && S.n<=5);
        cn[S.n-1]++;
        if(S.n<=4){
            auto a=adj(S);
            bool eligible=true;
            for(int i=0;i<S.n;i++)
                if(D[S.v[i]]+std::popcount(unsigned(a[i]))<5){eligible=false;break;}
            if(eligible) pending[S.n][mask(S)].push_back(S);
        }
        if(S.n==5){
            auto a=adj(S);
            for(int b=0;b<k;b++)if(good(S,a,b))return;
            write(6,S.v);
            return;
        }
        for(int i=0;i<S.n;i++)for(int x:nb[S.v[i]]){
            if(x<=S.v[0])continue;
            bool repeat=false;
            for(int j=0;j<S.n;j++)if(x==S.v[j]||(j<i&&E(x,S.v[j]))){repeat=true;break;}
            if(repeat) continue;
            Component T=S;
            T.v[T.n++]=x;
            for(int j=S.n;j>0 && T.v[j]<T.v[j-1];j--)std::swap(T.v[j],T.v[j-1]);
            auto a=adj(T);
            if(!fits(T,a)) continue;
            int added=int(std::find(T.v.begin(),T.v.begin()+T.n,x)-T.v.begin());
            // Retain only the canonical parent, whose removed vertex is
            // maximal among non-root removals leaving a connected graph.
            bool accept=true;
            for(int j=T.n-1;j>added;j--)
                if(isConnected(a, ((1<<T.n)-1)^(1<<j))){accept=false;break;}
            if(accept)walk(T);
        }
    }

    void makeGroups(){
        for(int s=1;s<=4;s++){
            I m=0;
            for(auto &x:pending[s]){
                m+=x.second.size();
                groups[s].push_back({x.first,std::move(x.second)});
            }
            std::cout<<"component size "<<s<<" count "<<m<<" mask types "<<groups[s].size()
                     <<" zero groups "<<(!groups[s].empty()&&groups[s][0].mask==0)<<std::endl;
            pending[s].clear();
            auto &w = acceptByWord[s];
            w.resize((groups[s].size()+63)/64);
            for(int i=0;i<int(groups[s].size());i++)
                for(int b=0;b<k;b++)
                    if((groups[s][i].mask>>b)&1)w[i/64][b]|=I{1}<<(i%64);
        }
    }
    bool separate(Component const&a,Component const&b)const{
        for(int i=0;i<a.n;i++)for(int j=0;j<b.n;j++)
            if(a.v[i]==b.v[j]||E(a.v[i],b.v[j]))return false;
        return true;
    }
    void instances(int shape,std::array<Group const*,5>const&gs,int count,int j,
                   Five& which,Five result,int off){
        assert(0<=j && j<=count && count<=5 && 0<=off && off<=5);
        if(j==count){assert(off==5);write(shape,result);return;}
        int start=0;
        if(j && gs[j]==gs[j-1])start=which[j-1]+1;
        auto const &l=gs[j]->list;
        for(int t=start;t<int(l.size());t++){
            tested[shape]++;
            bool ok=true;
            for(int i=0;i<j;i++)if(!separate(gs[i]->list[which[i]],l[t])){ok=false;break;}
            if(!ok)continue;
            which[j]=t;
            assert(1<=l[t].n && l[t].n<=4 && off+l[t].n<=5);
            for(int v=0;v<l[t].n;v++)result[off+v]=l[t].v[v];
            instances(shape,gs,count,j+1,which,result,off+l[t].n);
        }
    }
    void search(int shape,Five part,int nParts,int layer,std::array<Group const*,5>&gs,int start,I both){
        int size=part[layer];
        auto const &cur=groups[size];
        if(layer+1==nParts){
            auto const &byWord=acceptByWord[size];
            for(int w=start/64;w<int(byWord.size());w++){
                I pool=~I{0};
                if(w==start/64)pool<<=(start%64);
                if(w==int(byWord.size())-1 && cur.size()%64)
                    pool&=(I{1}<<(cur.size()%64))-1;
                // A terminal group is incompatible exactly when its mask
                // contains none of the prefix's still-successful colorings.
                for(I rem=both;rem && pool;rem&=rem-1)
                    pool&=~byWord[w][std::countr_zero(rem)];
                for(;pool;pool&=pool-1){
                    const auto id=64*w+std::countr_zero(pool);
                    assert(id<int(cur.size()) && !(both&cur[id].mask));
                    gs[layer]=&cur[id]; types[shape]++;
                    Five which{};
                    instances(shape,gs,nParts,0,which,{},0);
                }
            }
            return;
        }
        for(int j=start;j<int(cur.size());j++){
            gs[layer]=&cur[j];
            search(shape,part,nParts,layer+1,gs,part[layer+1]==size?j:0,both&cur[j].mask);
        }
    }
    void disconnected(){
        std::array<Five,6>parts{{{1,1,1,1,1},{2,1,1,1},{2,2,1},{3,1,1},{3,2},{4,1}}};
        for(int i=0;i<6;i++){
            std::array<Group const*,5> gs{};
            int nParts=int(std::count_if(parts[i].begin(),parts[i].end(),[](int a){return a!=0;}));
            search(i,parts[i],nParts,0,gs,0,bank);
            std::cout<<"disconnected shape "<<i<<" incompatible groups "<<types[i]
                     <<" checked component extensions "<<tested[i]
                     <<" residual "<<residual[i]<<std::endl;
        }
    }
};

int main(int argc,char**argv){
    assert(argc==3);
    Audit C(argv[1],argv[2]);
    std::cout<<"candidate vertices "<<C.n<<", bank "<<C.k<<std::endl;
    for(int i=0;i<C.n;i++) C.walk({1,{i}});
    std::cout<<"canonical connected visits by size";
    for(auto x:C.cn)std::cout<<" "<<x;
    std::cout<<"; connected 5 residual "<<C.residual[6]<<std::endl;
    C.makeGroups();
    C.disconnected();
}
