#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

using Int = __int128_t;
using UInt = __uint128_t;
using U64 = std::uint64_t;
using U8 = std::uint8_t;
using Coord = std::array<int,12>;

static U64 mix(U64 x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x^(x>>30))*0xbf58476d1ce4e5b9ULL;
    x = (x^(x>>27))*0x94d049bb133111ebULL;
    return x^(x>>31);
}
struct Hash {
    U64 operator()(Int p) const {
        auto v=UInt(p);
        return mix(U64(v)^mix(U64(v>>64)));
    }
};
using Keys=std::unordered_set<Int,Hash>;

static Int key(const Coord& q) {
    Int s=0;
    for (int i=0;i<12;++i) s+=Int(q[i])*(Int(1)<<(8*i));
    return s;
}
static Coord decode(Int k) {
    Coord q{};
    for (int& d:q) {
        Int r=k%256;
        if (r< -128) r+=256;
        if (r>=128) r-=256;
        d=int(r);
        k=(k-r)/256;
    }
    assert(k==0);
    return q;
}
static U64 choose5(U64 m) {
    if(m<5)return 0;
    assert(m<=546);
    U64 z=1;
    for(U64 i=0;i<5;++i) z=z*(m-i)/(i+1);
    return z;
}
static void checked_add(U64& a,U64 b) {
    assert(b<=std::numeric_limits<U64>::max()-a);
    a+=b;
}
struct Incidence {
    Int x;
    int j;
    bool operator<(const Incidence& r) const {
        if(x!=r.x)return x<r.x;
        return j<r.j;
    }
};
struct Rim {
    Int x;
    int base_degree;
    std::array<U8,64> masks{};
};
struct Audit {
    static constexpr std::size_t inc_cap=300000;
    int count_colors=0, shard=0, shard_count=0;
    Keys D,excluded;
    std::vector<Int> dirs,base;
    std::vector<Rim> candidates;
    std::vector<std::vector<int>> palettes;
    U64 generated=0, per_shard=0, kept=0, hubs=0, hubs5=0, raw=0, eligible=0, residual=0;
    U64 limit_visits=0;
    std::array<U64,64> hit{};
    std::ofstream out;

    Audit(const char* inp,const char* dst,int i,int n,U64 limit):
        shard(i),shard_count(n),limit_visits(limit),out(dst) {
        assert(out.good());
        assert(shard_count>=16 && std::has_single_bit(unsigned(shard_count)));
        assert(0<=shard && shard<shard_count);
        std::ifstream is(inp);
        assert(is.good());
        int bn=0, dn=0, actual_edges=0;
        assert(is>>bn>>dn>>count_colors>>actual_edges);
        assert(bn==449&&dn==546&&35<=count_colors&&count_colors<=64&&actual_edges==2198);
        int B=0, S=0;
        Keys old;
        for(int i0=0;i0<bn+dn;++i0) {
            Coord v{};
            for(int& x:v) {
                assert(is>>x);
                assert(-127<=x&&x<=127);
                int& cap=(i0<bn?B:S);
                cap=std::max(cap,std::abs(x));
            }
            auto z=key(v);
            assert(decode(z)==v);
            if(i0<bn) {
                assert(old.insert(z).second);
                base.push_back(z);
            } else {
                assert(z!=0 && D.insert(z).second);
                dirs.push_back(z);
            }
        }
        assert(B+2*S<128);
        // A packed equality in every operation below is coefficientwise:
        // for differences of two sums/differences being compared, each
        // coefficient is strictly between -256 and 256. Induct mod 256.
        assert(2*B+4*S<256);
        for(auto d:dirs)assert(D.contains(-d));
        palettes.resize(count_colors,std::vector<int>(bn));
        for(auto& bank:palettes) {
            unsigned used=0;
            for(int& v:bank) {
                assert(is>>v);
                assert(0<=v&&v<5);
                used|=1u<<v;
            }
            assert(used==31);
        }
        std::string extra;
        assert(!(is>>extra));
        int edges=0;
        for(int u=0;u<bn;++u)for(int v=u+1;v<bn;++v)
            if(D.contains(base[u]-base[v])) {
                ++edges;
                for(auto const& b:palettes)assert(b[u]!=b[v]);
            }
        assert(edges==actual_edges);
        std::vector<Incidence> T;
        T.reserve(std::size_t(bn)*dn);
        for(int i0=0;i0<bn;++i0)for(auto d:dirs)T.push_back({base[i0]+d,i0});
        std::sort(T.begin(),T.end());
        excluded.reserve(250000);
        excluded.insert(old.begin(),old.end());
        int outside=0;
        for(std::size_t beg=0;beg<T.size();) {
            std::size_t end=beg+1;
            auto x=T[beg].x;
            while(end<T.size()&&T[end].x==x) {
                assert(T[end-1].j<T[end].j);
                ++end;
            }
            if(!old.contains(x)) {
                ++outside;
                assert(excluded.insert(x).second);
                if(end-beg>=2) {
                    Rim r{x,int(end-beg),{}};
                    assert(r.base_degree<=9);
                    std::fill_n(r.masks.begin(),count_colors,U8(31));
                    for(std::size_t l=beg;l<end;++l)
                        for(int b=0;b<count_colors;++b)
                            r.masks[b]&=~(1u<<palettes[b][T[l].j]);
                    candidates.push_back(r);
                }
            }
            beg=end;
        }
        assert(outside==229320&&candidates.size()==7056);
    }

    bool colorable(std::array<int,5> const& A,std::array<U8,5> const& L,unsigned left) const {
        if(!left)return true;
        int i=-1, k=6;
        for(int j=0;j<5;++j)if(left&(1u<<j)) {
            int n=std::popcount(unsigned(L[j]));
            if(!n)return false;
            if(n<k){i=j;k=n;}
        }
        assert(i>=0);
        unsigned todo=left^(1u<<i);
        for(unsigned colors=L[i];colors;colors&=colors-1) {
            unsigned bit=colors&-colors;
            auto M=L;
            for(int j=0;j<5;++j)if(todo&unsigned(A[i])&(1u<<j))M[j]&=~bit;
            if(colorable(A,M,todo))return true;
        }
        return false;
    }
    void test(Int hub,std::vector<int> const& ids) {
        assert(ids.size()==5);
        if(++eligible>limit_visits) {
            std::cerr<<"Incomplete: per-shard eligible visit cap exceeded.\n";
            std::exit(5);
        }
        std::array<int,5> A{};
        for(int i=0;i<5;++i)for(int j=i+1;j<5;++j)
            if(D.contains(candidates[ids[i]].x-candidates[ids[j]].x)) {
                A[i]|=1<<j;
                A[j]|=1<<i;
            }
        for(int i=0;i<5;++i)
            assert(candidates[ids[i]].base_degree+std::popcount(unsigned(A[i]))>=4);
        for(int b=0;b<count_colors;++b) {
            for(unsigned h=1;h<=16;h<<=1) {
                std::array<U8,5> L{};
                for(int i=0;i<5;++i)L[i]=candidates[ids[i]].masks[b]&~h;
                if(colorable(A,L,31)) {
                    ++hit[b];
                    return;
                }
            }
        }
        if(++residual>50000) {
            std::cerr<<"Incomplete: per-shard residual output cap exceeded.\n";
            std::exit(6);
        }
        for(int x:decode(hub))out<<x<<' ';
        std::vector<int> sorted=ids;
        std::sort(sorted.begin(),sorted.end());
        for(int id:sorted)for(int x:decode(candidates[id].x))out<<x<<' ';
        out<<'\n';
        if(!out.good())std::exit(7);
    }

    using Choices=std::vector<std::vector<std::vector<int>>>;
    void combine(Int hub,int left,int start,Choices const& choices,std::vector<int> const& suffix,
                 std::vector<int>& ids) {
        if(left==0) {
            test(hub,ids);
            return;
        }
        for(int c=start;c<int(choices.size())&&suffix[c]>=left;++c) {
            for(auto const& take:choices[c]) {
                int n=take.size();
                assert(n>=1);
                if(n>left||suffix[c+1]<left-n)continue;
                ids.insert(ids.end(),take.begin(),take.end());
                combine(hub,left-n,c+1,choices,suffix,ids);
                ids.resize(ids.size()-n);
            }
        }
    }

    void around(Int hub,std::vector<int> const& ns) {
        ++hubs5;
        checked_add(raw,choose5(ns.size()));
        assert(ns.size()>=5&&ns.size()<=546);
        int n=ns.size();
        std::vector<std::vector<int>> G(n);
        for(int i=0;i<n;++i)for(int j=i+1;j<n;++j)
            if(D.contains(candidates[ns[i]].x-candidates[ns[j]].x)) {
                G[i].push_back(j);
                G[j].push_back(i);
            }
        for(auto const& g:G)assert(g.size()<=2);
        // Necessary monotone elimination: a b=2 rim needs both potential
        // unit-circle neighbors; a b=3 rim needs one. Remove impossible
        // vertices to a fixed point before enumerating component choices.
        std::vector<bool> live(n,true);
        for(bool changed=true;changed;) {
            changed=false;
            for(int i=0;i<n;++i)if(live[i]) {
                int d=0;
                for(int j:G[i])d+=live[j];
                if(candidates[ns[i]].base_degree+d<4) {
                    live[i]=false;
                    changed=true;
                }
            }
        }
        if(std::count(live.begin(),live.end(),true)<5)return;
        Choices choices;
        std::vector<int> maxsel;
        std::vector<bool> seen(n);
        for(int i=0;i<n;++i)if(live[i]&&!seen[i]) {
            std::vector<int> comp{i};
            seen[i]=true;
            for(std::size_t s=0;s<comp.size();++s)
                for(int j:G[comp[s]])if(live[j]&&!seen[j]) {
                    seen[j]=true;
                    comp.push_back(j);
                }
            assert(comp.size()<=6);
            std::vector<std::vector<int>> opts;
            int mx=0;
            for(unsigned m=1;m<(1u<<comp.size());++m) {
                int t=std::popcount(m);
                if(t>5)continue;
                std::vector<int> ids;
                for(unsigned j=0;j<comp.size();++j)if(m&(1u<<j)) {
                    int d=0;
                    for(unsigned k=0;k<comp.size();++k)if(m&(1u<<k))
                        d+=D.contains(candidates[ns[comp[j]]].x-candidates[ns[comp[k]]].x);
                    if(candidates[ns[comp[j]]].base_degree+d<4)break;
                    ids.push_back(ns[comp[j]]);
                }
                if(int(ids.size())==t) {
                    mx=std::max(mx,t);
                    opts.push_back(std::move(ids));
                }
            }
            if(mx>0) {
                choices.push_back(std::move(opts));
                maxsel.push_back(mx);
            }
        }
        std::vector<int> suffix(maxsel.size()+1);
        for(int i=int(maxsel.size())-1;i>=0;--i)suffix[i]=suffix[i+1]+maxsel[i];
        std::vector<int> current;
        combine(hub,5,0,choices,suffix,current);
    }
    void run() {
        std::vector<Incidence> H;
        H.reserve(inc_cap);
        Hash h;
        for(int j=0;j<int(candidates.size());++j)for(auto d:dirs) {
            auto x=candidates[j].x+d;
            ++generated;
            if((h(x)&(shard_count-1))!=unsigned(shard))continue;
            ++per_shard;
            if(excluded.contains(x))continue;
            if(H.size()==inc_cap) {
                std::cerr<<"Incomplete: incidence capacity exceeded; increase shard_count.\n";
                std::exit(4);
            }
            H.push_back({x,j});
        }
        assert(generated==3852576);
        kept=H.size();
        std::sort(H.begin(),H.end());
        for(std::size_t beg=0;beg<H.size();) {
            std::size_t end=beg+1;
            while(end<H.size()&&H[end].x==H[beg].x) {
                assert(H[end-1].j<H[end].j);
                ++end;
            }
            ++hubs;
            if(end-beg>=5) {
                std::vector<int> ns;
                for(std::size_t k=beg;k<end;++k)ns.push_back(H[k].j);
                around(H[beg].x,ns);
            }
            beg=end;
        }
        assert(std::accumulate(hit.begin(),hit.end(),U64(0))+residual==eligible);
        out.flush();
        if(!out.good())std::exit(7);
        std::cout<<"COMPLETE "<<shard<<'/'<<shard_count
                 <<" generated "<<generated<<" shard-incidences "<<per_shard
                 <<" retained "<<kept<<" hubs "<<hubs<<" hubs5 "<<hubs5
                 <<" raw5 "<<raw<<" eligible "<<eligible<<" residual "<<residual<<"\n";
        std::cout<<"first success counts:";
        for(int i=0;i<count_colors;++i)std::cout<<' '<<hit[i];
        std::cout<<"\n";
    }
};
int main(int argc,char**argv){
    if(argc!=6){
        std::cerr<<"Usage: zero_hub INPUT OUT SHARD SHARD_COUNT ELIGIBLE_VISIT_CAP\n";
        return 2;
    }
    int i=std::stoi(argv[3]), n=std::stoi(argv[4]);
    U64 limit=std::stoull(argv[5]);
    if(!limit)return 2;
    Audit a(argv[1],argv[2],i,n,limit);
    a.run();
}
