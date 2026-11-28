#!/usr/bin/env python3
"""Single pinned Lean replay with wall time and sampled RSS guards."""
import hashlib, os, pathlib, subprocess, sys, time
LEAN = pathlib.Path(sys.argv[1]).resolve()
assert hashlib.sha256(LEAN.read_bytes()).hexdigest() == 'db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
version = subprocess.check_output([str(LEAN),'--version'],timeout=3,text=True).strip()
assert 'version 4.36.0,' in version and '611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9' in version
pathlib.Path('replay-tmp').mkdir(exist_ok=True)
env = dict(os.environ)
env.pop('LEAN_PATH',None)
env['TMPDIR'] = str(pathlib.Path('replay-tmp').resolve())
env['LEAN_NUM_THREADS'] = '1'
with open('replay.log','w') as out:
    cmd = [str(LEAN), '--threads=1', '--tstack=16384', '--memory=1000', 'LayeredFive.lean']
    out.write(version+'\n')
    out.write('command: lean --threads=1 --tstack=16384 --memory=1000 LayeredFive.lean\n')
    out.flush()
    st=time.monotonic()
    p=subprocess.Popen(cmd,env=env,stdout=out,stderr=subprocess.STDOUT)
    rss=0
    while p.poll() is None:
        e=time.monotonic()-st
        try:
            stx=pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines()
            vals=[int(ln.split()[1]) for ln in stx if ln.startswith(('VmHWM:','VmRSS:'))]
            rss=max(rss,*vals) if vals else rss
        except FileNotFoundError:
            pass
        if e>20 or rss>1500000:
            p.kill();p.wait()
            out.write(f'stopped on guard: {e:.3f}s, sampled peak {rss} KiB\n')
            raise SystemExit(125)
        time.sleep(.025)
    out.write(f'exit {p.returncode}; {time.monotonic()-st:.3f}s; sampled peak {rss} KiB\n')
    raise SystemExit(p.returncode)
