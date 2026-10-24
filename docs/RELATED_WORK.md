# Relation to the announced lower bounds

The general comparison in this repository is with the formula

$$H(n)=n!+(n-1)!+(n-2)!+n-3+
\left\lceil\frac{2((n-2)!-(n-2))}{n^2-4n+1}\right\rceil.$$

Halfar's [6 October 2026 announcement](https://groups.google.com/g/superpermutators/c/6ozhk3faHDA)
attributes this formula to Cole Fritsch and describes its formal proof for
every $n\ge7$. The same announcement gives stronger bounds at individual
sizes, obtained from finite searches. Those values are not the formula $H$.

Our general formulas hold for every $n\ge8$. Like $H$, their leading
correction above $n!+(n-1)!+(n-2)!$ is asymptotic to $2(n-4)!$.
The proved differences from $H$ are asymptotic to $3(n-6)!$ when
$n\equiv1\pmod3$, $18(n-7)!$ when $n\equiv2\pmod3$, and
$9(n-7)!$ when $n\equiv0\pmod3$. The
[informal statement](INFORMAL_STATEMENT.md) also separates these comparisons
from the smaller improvements contributed by the new return-order argument.

The two finite results compare as follows with the
6 October announcement.

| Alphabet size | Halfar's announced bound | Bound submitted here | Difference |
| ---: | ---: | ---: | ---: |
| 10 | 4,033,378 | 4,033,379 | 1 |
| 14 | 93,891,141,008 | 93,891,141,150 | 142 |

This is a comparison with that dated announcement, not a claim to survey
every later source revision. The native-qualified thirteen-symbol certificate
discussed in the finite paper is outside this submission.

The ten-symbol result uses Halfar's chain-piece search, completeness, and
capacity framework. Our contribution is the stronger certificate and its
connection to the unrestricted word model. The fourteen-symbol refinement
uses a separate global compatibility argument. The inherited source and
licence notices credit Xiaolong Liu and the Hunter-Raudvere library;
see [NOTICE](../NOTICE) and [Halfar's notice](../licenses/Halfar-NOTICE).
The [pinned Halfar source](https://github.com/jhalfar/superpermutations/tree/cc5c763bd5854317b20dadb138990802656e6f03/proofs/lean/lower)
identifies the framework used in this development.
