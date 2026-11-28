import hashlib,json,os,resource,re,subprocess,sys,time
from pathlib import Path
R=Path('/workspace/scratch/fb47f17f885e')
C=R/'.lean-check'; M=C/'mathlib4'
A=Path('/tmp/es33/numbering-core/clean-room')
N=Path('/tmp/es33/numbering-core/release')
E=R/'es33-residual-extraction-check'
W=R/'es33-prelude-legacy-first-two'
stage=sys.argv[1]; cap=float(sys.argv[2])
known=('ActualGoodRows','CoverageInequalities')
assert stage in known
assert 'es33-unanchored.cnf: OK' in (N/'clean-replay.log').read_text()
dig=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
requirements=[]
for s in known[:known.index(stage)]:
    j=json.loads(Path(f'{s}.json').read_text())
    assert j['verified'] and j['exit']==0,s
    assert dig(Path(f'out/{s}.olean'))==j['olean_sha256'],s
    requirements.append((s,j['olean_sha256']))
L=R/'es33-literal-bridge-check'
geom=[]
for s in ('EndpointConcreteSpec','LiteralFamilies'):
    j=json.loads((L/f'{s}.json').read_text())
    assert j['verified'] and j['exit']==0,s
    assert dig(L/f'out/{s}.olean')==j['olean_sha256'],s
    requirements.append((s,j['olean_sha256']))
for s in ('NumberedCNF','EndpointGuardCore','EndpointBaseAliases'):
    requirements.append((s,dig(A/f'{s}.olean')))
os.environ['LEAN_PATH']=':'.join(map(str,[Path.cwd()/'out',L/'out',A,*geom]))
os.environ['TMPDIR']=str(Path.cwd()/'tmp')
src=Path(f'{stage}.lean'); out=Path(f'out/{stage}.olean')
assert not out.exists()
f=Path(f'{stage}.log')
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
req={'ActualGoodRows':('actual_goodRows','target32_goodRows'),
     'CoverageInequalities':('state_literal_present','width2_project','cap_extension_width','cup_extension_width')}[stage]
valid=rc==0 and out.is_file() and all(('ES33.EndpointConcrete.'+n) in audit for n in req) \
    and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in audit.values())
if rc==0 and not valid:reason='missing audit/object, or unexpected axioms'
r=resource.getrusage(resource.RUSAGE_CHILDREN)
rec={'module':stage,'verified':valid,'exit':rc,'reason':reason,'wall_s':round(time.monotonic()-t0,3),
     'maxRSS_kib':r.ru_maxrss,'sampled_peak_kib':peak,'user_s':round(r.ru_utime,3),
     'sys_s':round(r.ru_stime,3),'source_sha256':dig(src),'log_sha256':dig(f),'axioms':audit,
     'direct_prerequisite_objects':requirements}
if valid:rec['olean_sha256']=dig(out)
Path(f'{stage}.json').write_text(json.dumps(rec,indent=2)+'\n')
print(txt,end='');print(json.dumps(rec,indent=2),flush=True)
sys.exit(0 if valid else 1)
