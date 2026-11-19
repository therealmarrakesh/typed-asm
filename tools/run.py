"""Run a command with a time limit and a memory limit.

    python3 tools/run.py SECONDS COMMAND...

The command runs in a session of its own. If it is still running after
SECONDS, or if the resident memory of the command and everything it started
passes the cap, the whole group is killed. The cap is 16 GB; set RUN_CAP_GB
to change it. The command's output is printed when it ends, followed by one
line saying how long it took, the most memory it used, and how it ended.

A limit on address space is not used: Lean reserves far more address space
than it touches.
"""
import subprocess, time, os, signal, sys, tempfile
CAP_KB = int(float(os.environ.get('RUN_CAP_GB', '16')) * 1024 * 1024)
def group_rss_kb(sid):
    tot = 0; shared = 0   # private pages summed; pages shared between processes counted once
    for d in os.listdir('/proc'):
        if not d.isdigit(): continue
        try:
            with open('/proc/%s/stat' % d) as f: st = f.read()
            fields = st[st.rindex(')') + 2:].split()
            if int(fields[3]) != sid: continue          # session id
            with open('/proc/%s/statm' % d) as f: m = f.read().split()
            tot += (int(m[1]) - int(m[2])) * 4; shared = max(shared, int(m[2]) * 4)
        except Exception: pass
    return tot + shared
def run(cmd, to):
    t = time.time(); peak = 0
    out = tempfile.TemporaryFile(mode='w+')
    p = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
    why = None
    while p.poll() is None:
        time.sleep(0.2)
        rss = group_rss_kb(p.pid); peak = max(peak, rss)
        if rss > CAP_KB: why = "MEMORY CAP (%.1f GB resident)" % (rss / 1048576)
        elif time.time() - t > to: why = "TIMEOUT after %ds" % to
        if why:
            try: os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            p.wait(); break
    out.seek(0); sys.stdout.write(out.read())
    print("[%s%.1fs, peak %.1f GB, exit %s] %s" % ((why + ": group killed; ") if why else "",
          time.time() - t, peak / 1048576, p.returncode, ' '.join(cmd)[-60:]))
    return 124 if why else p.returncode
if __name__ == '__main__':
    sys.exit(run(sys.argv[2:], int(sys.argv[1])))
