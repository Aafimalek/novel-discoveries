import hashlib,json,os,resource,re,subprocess,sys,time
from pathlib import Path
R=Path('/workspace/scratch/fb47f17f885e')
C=R/'.lean-check'; M=C/'mathlib4'
A=Path('/tmp/es33/numbering-core/clean-room')
N=Path('/tmp/es33/numbering-core/release')
W=R/'es33-prelude-legacy-first-two'
stage=sys.argv[1]; cap=float(sys.argv[2])
names=('EndpointPacket','EndpointRecurrence','EndpointModel','RealChainValuation')
known=tuple(('ES33/'+n if i<3 else n) for i,n in enumerate(names))
assert stage in known
assert 'es33-unanchored.cnf: OK' in (N/'clean-replay.log').read_text()
dig=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prereq=(
(W/'olean/ES33/LocalCNF.olean','9a75b99d66de4b5e18e9431cb684d44fd12a485cdc3bbb84bcb6badf26c6d55d'),
(Path('src/ES33/EndpointPacket.lean'),'e328b3a259e97a15cb66c2c030c625c5fe1477af603b5fe224d9f3cca3766d6f'),
(Path('src/ES33/EndpointRecurrence.lean'),'123eaa0af56d68265011f4dde0974f873476ed283c7db383baa2c9006f4a3796'),
(Path('src/ES33/EndpointModel.lean'),'d0b7ed25834c3708e6ee38aaa9389d532028c024ecbe8ee5ffcdba0803807487'))
requirements=[]
for p, h in prereq:
    assert dig(p)==h,p
    requirements.append((str(p),h))
for mod in known[:known.index(stage)]:
    j=json.loads(Path(f'{Path(mod).name}.json').read_text())
    assert j['verified'] and j['exit']==0,mod
    assert dig(Path(f'out/{mod}.olean'))==j['olean_sha256'],mod
    requirements.append((mod,j['olean_sha256']))
L=R/'es33-literal-bridge-check'
for mod in ('EndpointConcreteSpec','LiteralFamilies'):
    j=json.loads((L/f'{mod}.json').read_text())
    assert j['verified'] and j['exit']==0,mod
    assert dig(L/f'out/{mod}.olean')==j['olean_sha256'],mod
    requirements.append((mod,j['olean_sha256']))
for mod in ('NumberedCNF','EndpointGuardCore','EndpointBaseAliases'):
    requirements.append((mod,dig(A/f'{mod}.olean')))
geom=[W/'olean',M/'.lake/build/lib/lean',*sorted((M/'.lake/packages').glob('*/.lake/build/lib/lean'))]
os.environ['LEAN_PATH']=':'.join(map(str,[Path.cwd()/'out',L/'out',A,*geom]))
os.environ['TMPDIR']=str(Path.cwd()/'tmp')
src=Path(f'src/{stage}.lean'); out=Path(f'out/{stage}.olean')
assert not out.exists()
f=Path(f'{Path(stage).name}.log')
lean=C/'lean-4.36.0-linux/bin/lean'
assert dig(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
cmd=[str(lean),'-j','1','-M','2250','-DwarningAsError=true','-o',str(out),str(src)]
rss_cap=2310000; reason=''; peak=0
t0=time.monotonic()
with f.open('wb') as h:
    p=subprocess.Popen(cmd,stdout=h,stderr=h)
    while p.poll() is None:
        try:
            cur=next(int(r.split()[1]) for r in Path(f'/proc/{p.pid}/status').read_text().splitlines() if r.startswith('VmRSS:'))
            peak=max(cur,peak)
            if cur>rss_cap:reason='RSS';p.kill();break
        except (FileNotFoundError,StopIteration):pass
        if time.monotonic()-t0>cap:reason='TIMEOUT';p.kill();break
        time.sleep(.05)
    rc=p.wait()
txt=f.read_text()
audit={m[1]:[x.strip() for x in m[2].split(',')] if m[2] else []
       for m in re.finditer(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])$",txt,re.M)}
req={
  'ES33/EndpointPacket':(),
  'ES33/EndpointRecurrence':('ES33.Endpoint.forward_exact',),
  'ES33/EndpointModel':('ES33.Endpoint.actual_propagates',),
  'RealChainValuation':tuple('ES33.EndpointConcrete.'+x for x in
     ('chainVal_signs','guard_propagation','chainVal_states','chainVal_cap_three',
      'chainVal_cup_three','chainVal_cap_pair','chainVal_cup_pair','chainVal_propagates',
      'real_chainVal_propagates'))}[stage]
valid=rc==0 and out.is_file() and all(n in audit for n in req) \
    and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in audit.values())
if rc==0 and not valid:reason='missing audit/object, or unexpected axioms'
r=resource.getrusage(resource.RUSAGE_CHILDREN)
rec={'module':stage,'verified':valid,'exit':rc,'reason':reason,'wall_s':round(time.monotonic()-t0,3),
     'maxRSS_kib':r.ru_maxrss,'sampled_peak_kib':peak,'user_s':round(r.ru_utime,3),
     'sys_s':round(r.ru_stime,3),'source_sha256':dig(src),'log_sha256':dig(f),'axioms':audit,
     'direct_prerequisite_objects':requirements}
if valid:rec['olean_sha256']=dig(out)
Path(f'{Path(stage).name}.json').write_text(json.dumps(rec,indent=2)+'\n')
print(txt,end='');print(json.dumps(rec,indent=2),flush=True)
sys.exit(0 if valid else 1)
