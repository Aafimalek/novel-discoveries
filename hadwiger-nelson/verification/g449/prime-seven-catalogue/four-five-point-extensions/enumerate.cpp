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

using Four = std::array<int,4>;
struct Component { int n; Four v; };
struct Group {I mask; std::vector<Component> list;};

struct Audit {
    int n,k,W;
    I bank;
    std::vector<int>D;
    std::vector<std::array<std::uint8_t,64>> lists;
    std::vector<std::vector<int>> nb;
    std::vector<I> matrix;
    std::vector<Group> g1, g2, g3;
    std::array<I,5> residual{}, types{}, tested{};
    std::array<I,4> cn{};
    I connected{0};
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
    std::array<int,4> adj(Component const &C) const{
        std::array<int,4> a{};
        for(int i=0;i<C.n;i++)for(int j=i+1;j<C.n;j++)if(E(C.v[i],C.v[j])){
            a[i]|=1<<j; a[j]|=1<<i;
        }
        return a;
    }
    bool colored(std::array<int,4> const&a,Four l,int left) const{
        if(!left) return true;
        int i=-1,min=6;
        for(int j=0;j<4;j++)if((left>>j)&1){
            int t=std::popcount(unsigned(l[j]));
            if(t==0) return false;
            if(t<min){min=t;i=j;}
        }
        assert(i>=0);
        for(unsigned available=l[i];available;available&=available-1){
            Four keep=l;
            int cl = 1<<std::countr_zero(available);
            int further=(left^(1<<i));
            for(int j=0;j<4;j++)if(((further&a[i])>>j)&1)keep[j]&=~cl;
            if(colored(a,keep,further)) return true;
        }
        return false;
    }
    bool good(Component const &C,std::array<int,4> const&a,int b) const {
        Four l{};
        for(int i=0;i<C.n;i++)l[i]=lists[C.v[i]][b];
        return colored(a,l,(1<<C.n)-1);
    }
    I mask(Component const&C) const {
        auto a=adj(C);
        I s=0;
        for(int b=0;b<k;b++) if(good(C,a,b)) s|=I{1}<<b;
        return s;
    }
    void write(int shape,Four r) {
        std::sort(r.begin(),r.end());
        assert(std::adjacent_find(r.begin(),r.end())==r.end());
        out<<shape;
        for(int i:r) out<<' '<<i;
        out<<'\n';
        residual[shape]++;
    }
    bool fits(Component const &T,std::array<int,4> const&a) const{
        int remaining=4-T.n;
        for(int j=0;j<T.n;j++)
            if(D[T.v[j]]+std::popcount(unsigned(a[j]))+remaining<5) return false;
        return true;
    }
    bool isConnected(std::array<int,4> const& a,int subset) const{
        assert(subset>0);
        int seen=subset&-subset;
        for(int j=0;j<3;j++) {
            int expanded=seen;
            for(int v=0;v<4;v++) if((seen>>v)&1)expanded|=(a[v]&subset);
            if(expanded==seen)break;
            seen=expanded;
        }
        return seen==subset;
    }
    void walk(Component const&S){
        assert(1<=S.n && S.n<=4);
        cn[S.n-1]++;
        if(S.n==4){
            connected++;
            auto a=adj(S);
            for(int b=0;b<k;b++)if(good(S,a,b))return;
            write(4,S.v);
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
    void makeGroups() {
        std::map<I,std::vector<Component>> a,b,c;
        for(int i=0;i<n;i++) if(D[i]>=5){Component s={1,{i}};a[mask(s)].push_back(s);}
        for(int i=0;i<n;i++) if(D[i]>=4)for(int j:nb[i])if(i<j && D[j]>=4){
            Component s={2,{i,j}};b[mask(s)].push_back(s);
        }
        for(int j=0;j<n;j++)if(D[j]>=3){
            for(int ii=0;ii<int(nb[j].size());ii++)for(int kk=ii+1;kk<int(nb[j].size());kk++){
                int i=nb[j][ii],k=nb[j][kk];
                if(E(i,k)){
                    if(j>i || j>k || D[i]<3 || D[k]<3)continue;
                }else{
                    if(D[i]<4 || D[k]<4)continue;
                }
                Component s={3,{i,j,k}};
                std::sort(s.v.begin(),s.v.begin()+3);
                c[mask(s)].push_back(s);
            }
        }
        auto pack=[](auto &from,std::vector<Group>&to,int s){
            I m=0;
            for(auto &x:from){m+=x.second.size();to.push_back({x.first,std::move(x.second)});}
            std::cout<<"component size "<<s<<" count "<<m<<" mask types "<<to.size()
                     <<" zero groups "<<(!to.empty()&&to[0].mask==0)<<'\n';
        };
        pack(a,g1,1);pack(b,g2,2);pack(c,g3,3);
    }
    bool separate(Component const&a,Component const&b)const{
        for(int i=0;i<a.n;i++)for(int j=0;j<b.n;j++)
            if(a.v[i]==b.v[j]||E(a.v[i],b.v[j]))return false;
        return true;
    }
    void instances(int shape,std::array<Group const*,4>const&groups,int count,int j,
                   std::array<int,4>&which,Four&outset,int off){
        assert(0<=j && j<=count && count<=4 && 0<=off && off<=4);
        if(j==count){assert(off==4);write(shape,outset);return;}
        int start=0;
        if(j && groups[j]==groups[j-1])start=which[j-1]+1;
        auto const &l=groups[j]->list;
        for(int t=start;t<int(l.size());t++){
            tested[shape]++;
            bool ok=true;
            for(int i=0;i<j;i++)if(!separate(groups[i]->list[which[i]],l[t])){ok=false;break;}
            if(!ok)continue;
            which[j]=t;
            assert(1<=l[t].n && l[t].n<=3 && off+l[t].n<=4);
            for(int v=0;v<l[t].n;v++)outset[off+v]=l[t].v[v];
            instances(shape,groups,count,j+1,which,outset,off+l[t].n);
        }
    }
    void incompatible(int shape,std::array<Group const*,4>const&gs,int count){
        types[shape]++;
        std::array<int,4> which{}; Four result{};
        instances(shape,gs,count,0,which,result,0);
    }
    void disconnected(){
        int x=int(g1.size()),y=int(g2.size());
        for(int a=0;a<x;a++)for(int b=a;b<x;b++){
            I p=g1[a].mask&g1[b].mask;
            for(int c=b;c<x;c++){
                I q=p&g1[c].mask;
                for(int d=c;d<x;d++)if(!(q&g1[d].mask))
                    incompatible(0,{&g1[a],&g1[b],&g1[c],&g1[d]},4);
            }
        }
        for(auto const &a:g2)
            for(int b=0;b<x;b++)for(int c=b;c<x;c++)
                if(!(a.mask&g1[b].mask&g1[c].mask))
                    incompatible(1,{&a,&g1[b],&g1[c]},3);
        for(int a=0;a<y;a++)for(int b=a;b<y;b++)
            if(!(g2[a].mask&g2[b].mask))incompatible(2,{&g2[a],&g2[b]},2);
        for(auto const&a:g3)for(auto const&b:g1)
            if(!(a.mask&b.mask))incompatible(3,{&a,&b},2);
    }
};

int main(int argc,char**argv){
    assert(argc==3);
    Audit C(argv[1],argv[2]);
    std::cout<<"candidate vertices "<<C.n<<", bank "<<C.k<<std::endl;
    C.makeGroups();
    std::cout<<std::flush;
    for(int i=0;i<C.n;i++) C.walk({1,{i}});
    std::cout<<"canonical connected visits by size";
    for(auto x:C.cn)std::cout<<" "<<x;
    std::cout<<"; connected 4 residual "<<C.residual[4]<<std::endl;
    C.disconnected();
    for(int i=0;i<4;i++)
        std::cout<<"disconnected shape "<<i<<" incompatible groups "<<C.types[i]
        <<" checked component extensions "<<C.tested[i]<<" residual "<<C.residual[i]<<std::endl;
}
