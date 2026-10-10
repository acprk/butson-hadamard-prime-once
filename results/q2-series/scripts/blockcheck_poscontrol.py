# Positive control for blockcheck.c (Theorem E1, n = 36): random generalized Frank sequences
#   a(6j+k) = zeta_6^(pi(k) j + psi(k)),  a genuine BH(Z_36, 6),
# are fed to "blockcheck 6 t". They must pass the same block filter and be reported perfect.
# usage: python3 blockcheck_poscontrol.py [path/to/blockcheck] [count]
import random, subprocess, sys
exe = sys.argv[1] if len(sys.argv) > 1 else './blockcheck'
cnt = int(sys.argv[2]) if len(sys.argv) > 2 else 20
random.seed(5)
ok = 0
for _ in range(cnt):
    pi = list(range(6)); random.shuffle(pi); psi = [random.randrange(6) for _ in range(6)]
    ex = [(pi[k] * j + psi[k]) % 6 for m in range(36) for (j, k) in [divmod(m, 6)]]
    out = subprocess.run([exe, '6', 't'], input=' '.join(map(str, ex)), capture_output=True, text=True).stdout
    last = out.strip().splitlines()[-1]
    good = 'perfect 0' not in last and 'perfect' in last
    ok += good
    print(pi, psi, '|', last)
print('positive control: %d/%d generalized Frank BH(Z36,6) found perfect by blockcheck' % (ok, cnt))
