#include <array>
#include <cstdint>
#include <chrono>
#include <iostream>
using namespace std;
constexpr int LIM=148, WIDTH=1+2*9*LIM/64;
using Mask=array<uint64_t, WIDTH>;
int bound, mode; uint64_t nodes;
Mask newmask(const Mask& d,int a,int s){
  Mask out=d;
  int order=(2*(s+a))/64;
  int qo=a/64,ro=a%64,q2=2*a/64,r2=2*a%64;
  for(int j=0;j<=order;j++){
    if (j>=qo){out[j]|=d[j-qo]<<ro;if(ro&&j>qo)out[j]|=d[j-qo-1]>>(64-ro);}
    if (j>=q2){out[j]|=d[j-q2]<<r2;if(r2&&j>q2)out[j]|=d[j-q2-1]>>(64-r2);}
  }
  return out;
}
inline bool used(const Mask& d,int i){return (d[i/64]>>(i%64))&1;}
bool check(int n, int hi, int s,int q,const Mask& d){
  nodes++;
  if(!n)return s>=511&&q>=bound;
  if(hi<n)return false;
  int g=1;
  if(mode>=2)while(g<=hi&&used(d,s+g))g++;
  int x=hi,ss=s,qq=q;
  for(int j=0;j<n;j++){
    if(mode>=1)while(x>0&&used(d,s+x)) --x;
    if(x<=0)return false;
    ss+=x;qq+=x*x;x-=g;
  }
  if(ss<511||qq<bound)return false;
  for(int a=hi;a>=n;--a){
    int ts=s+a,tq=q+a*a;
    for(int j=1;j<n;j++){int b=a-j;if(b<1)break;ts+=b;tq+=b*b;}
    if(ts<511||tq<bound)break;
    if(!used(d,s+a)&&check(n-1,a-1,s+a,q+a*a,newmask(d,a,s)))return true;
  }
  return false;
}
// CLI: cutoff followed by the complete already selected prefix.
int main(int argc,char** argv){
  if(argc<3||argc>10)return 2;
  bound=stoi(argv[1]); mode=0;
  Mask d{}; d[0]=1;
  int total=0,square=0,last=149;
  for(int i=2;i<argc;++i){
    int a=stoi(argv[i]);
    if(a<1||a>=last||a>148)return 2;
    d=newmask(d,a,total);
    total+=a;
    square+=a*a;
    last=a;
  }
  bool witness=check(11-argc,last-1,total,square,d);
  cout<<nodes<<' '<<witness<<'\n';
}
