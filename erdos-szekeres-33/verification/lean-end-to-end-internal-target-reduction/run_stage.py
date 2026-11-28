import hashlib,json,os,resource,re,subprocess,sys,time
from pathlib import Path
R=Path('/workspace/scratch/fb47f17f885e')
C=R/'.lean-check'; M=C/'mathlib4'
A=Path('/tmp/es33/numbering-core/clean-room')
N=Path('/tmp/es33/numbering-core/release')
W=R/'es33-prelude-legacy-first-two'
stage=sys.argv[1]; cap=float(sys.argv[2])
known=('ES33/EndpointExclusionGeometry','RealChainExclusions')
assert stage in known
assert 'es33-unanchored.cnf: OK' in (N/'clean-replay.log').read_text()
dig=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
V=R/'es33-real-chain-valuation-check'
L=R/'es33-literal-bridge-check'
G=R/'es33-whole-coverage-check'
S=R/'es33-goodrows-check'
E=R/'es33-residual-extraction-check'
pairs=[(V,'ES33/EndpointPacket'),(V,'ES33/EndpointRecurrence'),(V,'ES33/EndpointModel')]
if stage=='RealChainExclusions':
    pairs += [(Path.cwd(),'ES33/EndpointExclusionGeometry'),(V,'RealChainValuation'),
              (L,'EndpointConcreteSpec'),(L,'LiteralFamilies'),(L,'RealLiteralConnector'),
              (G,'ActualCoverage'),(G,'ActualRealConnector'),(E,'RealResidualExtraction'),
              (S,'ActualGoodRows'),(S,'CoverageInequalities')]
requirements=[]
for base,mod in pairs:
    j=json.loads((base/f'{Path(mod).name}.json').read_text())
    assert j['verified'] and j['exit']==0,mod
    assert dig(base/f'out/{mod}.olean')==j['olean_sha256'],mod
    if mod.startswith('ES33/'):
        assert dig(Path(f'out/{mod}.olean'))==j['olean_sha256'],mod
    requirements.append((mod,j['olean_sha256']))
for mod in ('NumberedCNF','EndpointGuardCore','EndpointBaseAliases'):
    requirements.append((mod,dig(A/f'{mod}.olean')))
assert dig(Path('out/ES33/AnchorReduction.olean'))==dig(W/'olean/ES33/AnchorReduction.olean')
geom=[W/'olean',M/'.lake/build/lib/lean',*sorted((M/'.lake/packages').glob('*/.lake/build/lib/lean'))]
os.environ['LEAN_PATH']=':'.join(map(str,[Path.cwd()/'out',V/'out',G/'out',S/'out',E/'out',L/'out',A,*geom]))
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
  'ES33/EndpointExclusionGeometry':tuple('ES33.Endpoint.'+x for x in
     ('Ends.to_set','union_even_and_inter','even_set_of_endpoint_pair','positive_set_of_cup')),
  'RealChainExclusions':tuple('ES33.EndpointConcrete.'+x for x in
     ('chainVal_excludes32','real_residual_satisfies_target32','es33_of_internal_target32_unsat'))}[stage]
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
