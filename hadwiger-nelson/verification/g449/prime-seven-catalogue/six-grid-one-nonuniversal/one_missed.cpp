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
static U64 choose4(U64 m) {
    if(m<4)return 0;
    assert(m<=546);
    U64 z=1;
    for(U64 i=0;i<4;++i) z=z*(m-i)/(i+1);
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
    Keys D;
    std::vector<Incidence> hub_base;
    std::vector<Int> dirs,base;
    std::vector<Rim> candidates;
    std::vector<std::vector<int>> palettes;
    U64 generated=0, per_shard=0, kept=0, hubs=0, hubs4=0, raw=0, eligible=0;
    std::array<U64,3> tested{}, residual{};
    static constexpr int h5n=574, words=(h5n+63)/64;
    using Bits=std::array<U64,words>;
    std::vector<std::vector<int>> missed;
    std::vector<int> high5, h5id;
    std::vector<Bits> no_contact;
    std::array<Bits,64> available{};
    U64 limit_visits=0;
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
        hub_base.reserve(222264);
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
                if(end-beg==1) {
                    assert(hub_base.empty() || hub_base.back().x<x);
                    hub_base.push_back({x,T[beg].j});
                } else {
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
        assert(outside==229320&&candidates.size()==7056&&hub_base.size()==222264);
        missed.resize(candidates.size());
        no_contact.resize(candidates.size());
        h5id.assign(candidates.size(),-1);
        for(int z=0;z<int(candidates.size());++z)if(candidates[z].base_degree>=5) {
            int id=high5.size();
            assert(id<h5n);
            high5.push_back(z);
            h5id[z]=id;
            for(int b=0;b<count_colors;++b)if(candidates[z].masks[b])
                add_bit(available[b],id);
        }
        assert(int(high5.size())==h5n);
        for(int z=0;z<int(candidates.size());++z) {
            if(h5id[z]>=0)add_bit(no_contact[z],h5id[z]);
            auto x=candidates[z].x;
            for(auto d:dirs) {
                auto it=std::lower_bound(candidates.begin(),candidates.end(),x+d,
                                         [](const Rim& r,Int y){return r.x<y;});
                if(it==candidates.end()||it->x!=x+d||it->base_degree<3)continue;
                int id=it-candidates.begin();
                missed[z].push_back(id);
                if(h5id[id]>=0)add_bit(no_contact[z],h5id[id]);
            }
            std::sort(missed[z].begin(),missed[z].end());
            assert(std::adjacent_find(missed[z].begin(),missed[z].end())==missed[z].end());
        }

    }

    static void add_bit(Bits& x,int j) {
        assert(0<=j&&j<h5n);
        x[j/64]|=U64(1)<<(j%64);
    }
    static U64 sum_bits(const Bits& x) {
        U64 z=0;
        for(auto w:x)z+=std::popcount(w);
        return z;
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
    auto find_hub(Int hub) const {
        return std::lower_bound(hub_base.begin(),hub_base.end(),Incidence{hub,-1});
    }
    void emit(Int hub,const std::vector<int>& ids,int w,int t) {
        assert(0<=t&&t<=2);
        if(++residual[t]>50000) {
            std::cerr<<"Incomplete: per-shard residual output cap exceeded.\n";
            std::exit(6);
        }
        for(int x:decode(hub))out<<x<<' ';
        std::vector<int> sorted=ids;
        std::sort(sorted.begin(),sorted.end());
        for(int id:sorted)for(int x:decode(candidates[id].x))out<<x<<' ';
        for(int x:decode(candidates[w].x))out<<x<<' ';
        out<<'\n';
        if(!out.good())std::exit(7);
    }
    void test(Int hub,std::vector<int> const& ids,const Bits& near_hub) {
        assert(ids.size()==4);
        if(++eligible>limit_visits) {
            std::cerr<<"Incomplete: per-shard eligible rim-set cap exceeded.\n";
            std::exit(5);
        }
        std::array<int,5> A{};
        for(int i=0;i<4;++i)for(int j=i+1;j<4;++j)
            if(D.contains(candidates[ids[i]].x-candidates[ids[j]].x)) {
                A[i]|=1<<j;
                A[j]|=1<<i;
            }
        unsigned need=0;
        for(int i=0;i<4;++i) {
            int t=candidates[ids[i]].base_degree+std::popcount(unsigned(A[i]));
            assert(t>=3);
            if(t==3)need|=1u<<i;
        }
        if(std::popcount(need)>2)return;
        auto it=find_hub(hub);
        assert(it!=hub_base.end()&&it->x==hub);
        int orig=it->j;
        U64 support=0;
        for(int b=0;b<count_colors;++b) {
            unsigned forbid=1u<<palettes[b][orig];
            for(unsigned h=1;h<=16;h<<=1)if(h!=forbid) {
                std::array<U8,5> L{};
                for(int i=0;i<4;++i)L[i]=candidates[ids[i]].masks[b]&~h;
                if(colorable(A,L,15)) {
                    support|=U64(1)<<b;
                    break;
                }
            }
        }
        if(!need) {
            Bits good{};
            for(int k=0;k<words;++k) {
                U64 bad=near_hub[k];
                for(int i:ids)bad|=no_contact[i][k];
                good[k]=~bad;
            }
            if(h5n%64)good.back()&=(U64(1)<<(h5n%64))-1;
            checked_add(tested[0],sum_bits(good));
            for(U64 choices=support;choices&&sum_bits(good);choices&=choices-1) {
                int b=std::countr_zero(choices);
                for(int k=0;k<words;++k)good[k]&=~available[b][k];
            }
            for(int k=0;k<words;++k)
                for(auto m=good[k];m;m&=m-1)
                    emit(hub,ids,high5[64*k+std::countr_zero(m)],0);
        }
        for(int i=0;i<4;++i)for(int w:missed[ids[i]]) {
            auto x=candidates[w].x;
            if(D.contains(x-hub)||std::find(ids.begin(),ids.end(),w)!=ids.end())continue;
            unsigned touch=0;
            for(int j=0;j<4;++j)
                if(D.contains(x-candidates[ids[j]].x))touch|=1u<<j;
            assert(touch);
            // Canonical owner is the first contacted rim in this selection.
            if(std::countr_zero(touch)!=i)continue;
            auto t=std::popcount(touch);
            assert(t<=2);
            if((need&~touch)||candidates[w].base_degree+t<5)continue;
            if(tested[1]+tested[2]>=5000000) {
                std::cerr<<"Incomplete: per-shard attached completion cap exceeded.\n";
                std::exit(8);
            }
            ++tested[t];
            auto B=A;
            B[4]=touch;
            for(int j=0;j<4;++j)if(touch&(1u<<j))B[j]|=16;
            bool ok=false;
            for(U64 choices=support;choices&&!ok;choices&=choices-1) {
                int b=std::countr_zero(choices);
                unsigned forbid=1u<<palettes[b][orig];
                if(!candidates[w].masks[b])continue;
                for(unsigned h=1;h<=16&&!ok;h<<=1)if(h!=forbid) {
                    std::array<U8,5> L{};
                    for(int j=0;j<4;++j)L[j]=candidates[ids[j]].masks[b]&~h;
                    L[4]=candidates[w].masks[b]; // no edge hub--missed
                    ok=colorable(B,L,31);
                }
            }
            if(!ok)emit(hub,ids,w,t);
        }
    }
    using Choices=std::vector<std::vector<std::vector<int>>>;
    void combine(Int hub,int left,int start,Choices const& choices,std::vector<int> const& suffix,
                 std::vector<int>& ids,const Bits& near_hub) {
        if(left==0) {
            test(hub,ids,near_hub);
            return;
        }
        for(int c=start;c<int(choices.size())&&suffix[c]>=left;++c) {
            for(auto const& take:choices[c]) {
                int n=take.size();
                assert(n>=1);
                if(n>left||suffix[c+1]<left-n)continue;
                ids.insert(ids.end(),take.begin(),take.end());
                combine(hub,left-n,c+1,choices,suffix,ids,near_hub);
                ids.resize(ids.size()-n);
            }
        }
    }

    void around(Int hub,std::vector<int> const& ns) {
        ++hubs4;
        checked_add(raw,choose4(ns.size()));
        assert(ns.size()>=4&&ns.size()<=546);
        Bits near_hub{};
        for(int i:ns)if(h5id[i]>=0)add_bit(near_hub,h5id[i]);
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
                if(candidates[ns[i]].base_degree+d<3) {
                    live[i]=false;
                    changed=true;
                }
            }
        }
        if(std::count(live.begin(),live.end(),true)<4)return;
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
                if(t>4)continue;
                std::vector<int> ids;
                for(unsigned j=0;j<comp.size();++j)if(m&(1u<<j)) {
                    int d=0;
                    for(unsigned k=0;k<comp.size();++k)if(m&(1u<<k))
                        d+=D.contains(candidates[ns[comp[j]]].x-candidates[ns[comp[k]]].x);
                    if(candidates[ns[comp[j]]].base_degree+d<3)break;
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
        combine(hub,4,0,choices,suffix,current,near_hub);
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
            auto it=find_hub(x);
            if(it==hub_base.end()||it->x!=x)continue;
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
            if(end-beg>=4) {
                std::vector<int> ns;
                for(std::size_t k=beg;k<end;++k)ns.push_back(H[k].j);
                around(H[beg].x,ns);
            }
            beg=end;
        }
        for(int i=0;i<3;++i)assert(residual[i]<=tested[i]);
        out.flush();
        if(!out.good())std::exit(7);
        std::cout<<"COMPLETE "<<shard<<'/'<<shard_count
                 <<" generated "<<generated<<" shard-incidences "<<per_shard
                 <<" retained "<<kept<<" hubs "<<hubs<<" hubs4 "<<hubs4
                 <<" raw4 "<<raw<<" eligible "<<eligible<<"\n";
        std::cout<<"tested "<<tested[0]<<' '<<tested[1]<<' '<<tested[2]
                 <<" residual "<<residual[0]<<' '<<residual[1]<<' '<<residual[2]<<"\n";
    }
};
int main(int argc,char**argv){
    if(argc!=6){
        std::cerr<<"Usage: one_missed INPUT OUT SHARD SHARD_COUNT ELIGIBLE_VISIT_CAP\n";
        return 2;
    }
    int i=std::stoi(argv[3]), n=std::stoi(argv[4]);
    U64 limit=std::stoull(argv[5]);
    if(!limit)return 2;
    Audit a(argv[1],argv[2],i,n,limit);
    a.run();
}
