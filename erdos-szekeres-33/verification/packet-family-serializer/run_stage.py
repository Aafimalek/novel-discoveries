import hashlib,json,os,resource,re,subprocess,sys,time
from pathlib import Path
R=Path('/workspace/scratch/fb47f17f885e')
C=R/'.lean-check'; M=C/'mathlib4'
A=Path('/tmp/es33/numbering-core/clean-room')
N=Path('/tmp/es33/numbering-core/release')
E=R/'es33-residual-extraction-check'
W=R/'es33-prelude-legacy-first-two'
stage=sys.argv[1]; cap=float(sys.argv[2])
known=('PacketFamilySerializer','SideRankSpec')
assert stage in known
dig=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=R/'es33-literal-bridge-check'; S=R/'es33-goodrows-check'; G=R/'es33-whole-coverage-check'
P=R/'es33-orientation-rank-check'
requirements=[('NumberedCNF',dig(A/'NumberedCNF.olean'))]
assert requirements[0][1]=='543f7f3d15c4db3452d84d80c4e59f8ca697fec2619d165ec41bc6d8298c7041'
pairs=[(P,'OrientationRank'),(L,'EndpointConcreteSpec')]
paths=[Path.cwd()/'out',P/'out',A,L/'out']
if stage=='PacketFamilySerializer':
    pairs.extend(((L,'LiteralFamilies'),(S,'ActualGoodRows'),(S,'CoverageInequalities'),(G,'ActualCoverage')))
    paths.extend([G/'out',S/'out'])
for base,mod in pairs:
    j=json.loads((base/f'{mod}.json').read_text())
    assert j['verified'] and j['exit']==0,mod
    assert dig(base/f'out/{mod}.olean')==j['olean_sha256'],mod
    requirements.append((mod,j['olean_sha256']))
os.environ['LEAN_PATH']=':'.join(map(str,paths))
os.environ['TMPDIR']=str(Path.cwd()/'tmp')
src=Path(f'{stage}.lean'); out=Path(f'out/{stage}.olean')
assert not out.exists()
f=Path(f'{stage}.log')
lean=C/'lean-4.36.0-linux/bin/lean'
assert dig(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
cmd=[str(lean),'-j','1','-M','2250','-DwarningAsError=true','-o',str(out),str(src.resolve())]
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
  'PacketFamilySerializer':tuple('ES33.EndpointConcrete.PacketFamilySerializer.'+x for x in
     ('encode_packet_family','compile_eq_encode','compiled_packet_suffix','packet_token_roundtrip',
      'render_compiled_suffix','packet_rows_in_compiled')),
  'SideRankSpec':()}[stage]
valid=rc==0 and out.is_file() and all(n in audit for n in req) \
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
