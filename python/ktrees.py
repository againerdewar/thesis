from sage.all import *
import sys

# Take arguments from the command line
args = sys.argv

assert len(args) == 3

kval = int(args[1])
nval = int(args[2])

# Set up a ring of formal power series
psr = PowerSeriesRing(QQ, 'x')
x = psr.gen()

# Compute the generating function for unlabeled Y-rooted k-trees fixed by permutations of a given cycle type mu.
# Note that mu should partition k
@cached_function
def unlY(mu, n):
    if n <= 0:
        return psr(1)
    else:
        ystretcher = lambda c, part: unlY(Partition(partition_power(part, c)), floor((n-1)/c)).subs({x:x**c})
        descendant_pseries = lambda part: prod(ystretcher(c, part) for c in part)
        return sum(x**i/i * descendant_pseries(partition_power(mu, i)).subs({x:x**i}) for i in xrange(1, n+1)).exp(n+1)

# Compute the generating function for unlabeled XY-rooted k-trees fixed by permutations of a given cycle type mu.
# Note that mu should partition k+1
@cached_function
def unlXY(mu, n):
    if n <= 0:
        return psr(0)
    else:
        ystretcher = lambda c: unlY(Partition(partition_power(mu, c)[:-1]), floor((n-1)/c)).subs({x:x**c})
        return (x * prod(ystretcher(c) for c in mu)).add_bigoh(n+1)

# Compute the generating functions for unlabeled X-, Y-, and XY-rooted k-trees using quotients
ax = lambda k, n: sum(1/mu.aut() * unlXY(mu, n) for mu in Partitions(k+1))
ay = lambda k, n: sum(1/mu.aut() * unlY(mu, n) for mu in Partitions(k))
axy = lambda k, n: sum(1/mu.aut() * unlXY(Partition(mu + [1]), n) for mu in Partitions(k))

# Compute the generating function for unlabeled un-rooted k-trees using the dissymmetry theorem
a = lambda k, n: ax(k, n) + ay(k, n) - axy(k, n)

# Print the result
print a(kval, nval)
