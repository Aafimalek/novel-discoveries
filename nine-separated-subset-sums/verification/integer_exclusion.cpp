#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
using namespace std;
constexpr int N=9, LIMIT=148, W=1+N*LIMIT/64;
using Bits=array<uint64_t,W>;
uint64_t nodes[N+1]{};
int upperSum[10][149]{}, upperSq[10][149]{};
int chosen[N]{};
bool search(int n,int hi,int sum,int sq,const Bits& bits) {
  ++nodes[n];
  if (!n) return true;
  if(hi<n || sum+upperSum[n][hi]<511 || sq+upperSq[n][hi]<87381) return false;
  for(int a=hi;a>=n;--a){
    if(sum+a+upperSum[n-1][a-1]<511 || sq+a*a+upperSq[n-1][a-1]<87381) break;
    Bits next=bits;
    bool collide=false;
    int q=a/64, r=a%64, end=(sum+a)/64;
    for(int j=q;j<=end;++j){
      uint64_t z=bits[j-q]<<r;
      if(r && j>q) z|=bits[j-q-1]>>(64-r);
      if(z & bits[j]){collide=true;break;}
      next[j]|=z;
    }
    if(!collide){
      chosen[n-1]=a;
      if(search(n-1,a-1,sum+a,sq+a*a,next))return true;
    }
  }
  return false;
}
int main(int argc,char**argv){
  for(int n=1;n<=N;++n)for(int a=n;a<=LIMIT;++a){
    upperSum[n][a]=a+upperSum[n-1][a-1];
    upperSq[n][a]=a*a+upperSq[n-1][a-1];
  }
  const int low=argc>1?stoi(argv[1]):1,high=argc>2?stoi(argv[2]):LIMIT;
  if(low<1||high>LIMIT||high<low)throw invalid_argument("expected 1 <= low <= high <= 148");
  for(int m=low;m<=high;++m){
    Bits root{};root[0]=1;root[m/64]|=uint64_t(1)<<(m%64);chosen[8]=m;
    if(search(N-1,m-1,m,m*m,root)){
      cout<<"FOUND at "<<m<<": ";for(int a:chosen)cout<<a<<' ';cout<<'\n';return 1;
    }
    if(m%4==0 || m==high){cout<<"Cleared through "<<m<<" nodes by remaining depth:";for(auto n:nodes)cout<<' '<<n;cout<<endl;}
  }
}
