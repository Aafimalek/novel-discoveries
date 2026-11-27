// Independent audit of the exact 32-point witness via convex hull sizes only.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct Point {
    int64_t x,y;
};

__int128 orient(Point a,Point b,Point c) {
    return (__int128(b.x)-a.x)*(__int128(c.y)-a.y)
         - (__int128(b.y)-a.y)*(__int128(c.x)-a.x);
}

int hull(std::array<Point,7> const& v,int n) {
    std::array<Point,15> st;
    int m=0;
    for (int i=0;i<n;i++){
        while(m>=2 && orient(st[m-2],st[m-1],v[i])<=0) --m;
        st[m++]=v[i];
    }
    int bottom=m;
    for (int i=n-2;i>=0;i--){
        while(m>bottom && orient(st[m-2],st[m-1],v[i])<=0) --m;
        st[m++]=v[i];
    }
    return m-1;
}

void verify_size(std::vector<Point> const& p,int target) {
    std::array<Point,7> sub;
    uint64_t cases=0,convex=0;
    auto rec=[&](auto&& self,int depth,int first)->void{
        if(depth==target){
            ++cases;
            convex += hull(sub,target)==target;
            return;
        }
        for(int i=first;i<=static_cast<int>(p.size())-(target-depth);i++){
            sub[depth]=p[i];
            self(self,depth+1,i+1);
        }
    };
    rec(rec,0,0);
    std::cout << "size " << target << ": " << cases << " checked, " << convex << " convex\n";
    if(target==6) assert(cases==906192 && convex==39648);
    if(target==7) assert(cases==3365856 && convex==0);
}

int main(int argc,char** argv){
    if(argc!=2) return 2;
    std::ifstream in(argv[1]);
    std::string line;
    std::getline(in,line);
    assert(line=="x,y");
    std::vector<Point> p;
    while(std::getline(in,line)){
        auto pos=line.find(',');
        assert(pos!=std::string::npos);
        p.push_back({std::stoll(line.substr(0,pos)),std::stoll(line.substr(pos+1))});
    }
    assert(p.size()==32);
    for(int i=0;i<31;i++) assert(p[i].x<p[i+1].x);
    int triples=0;
    for(int i=0;i<32;i++) for(int j=i+1;j<32;j++) for(int k=j+1;k<32;k++){
        assert(orient(p[i],p[j],p[k])!=0);
        ++triples;
    }
    std::cout << triples << " noncollinear triples\n";
    verify_size(p,6);
    verify_size(p,7);
}
