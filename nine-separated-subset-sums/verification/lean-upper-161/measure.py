import resource, subprocess, sys, time
started = time.monotonic()
proc = subprocess.run(sys.argv[1:])
stats = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f'EXIT {proc.returncode}; wall seconds {time.monotonic()-started:.4f}; peak child RSS KiB {stats.ru_maxrss}')
sys.exit(proc.returncode if proc.returncode >= 0 else 128-proc.returncode)
