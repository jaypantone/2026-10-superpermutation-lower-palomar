# Lower bounds for superpermutations

The research presented here, the Lean formalization, and this document were generated entirely by AI systems under Jay Pantone’s direction. The inherited mathematical work and software retain their original credits. Independent AI review is not human peer review.

A superpermutation on $n$ symbols is a word containing every permutation of those symbols as a consecutive subword. Write $S(n)$ for the shortest possible length, and put

$$
F_3(n)=n!+(n-1)!+(n-2)!.
$$

The main result is an explicit lower bound $B(n)$ for every $n\ge8$. Its correction above $F_3(n)$ is asymptotic to $2(n-4)!$. The improvement lies in the smaller terms: we prove precise gains over the Fritsch–Halfar general formula in all three residue classes modulo three. We also prove the individual bounds

$$
S(10)\ge4\,033\,379,
\qquad
S(14)\ge93\,891\,141\,150.
$$

All these lower bounds apply to arbitrary superpermutations. In the formal statements, a word is a list over `Fin n`, and coverage means that every list of $n$ distinct symbols occurs as a consecutive sublist.

## Why the general bound improves

Large overlaps make a superpermutation short. The cheapest step appends one symbol and moves to the next cyclic rotation of a permutation. These rotations can be grouped into classes, then into runs and chains. Earlier estimates describe how efficiently the chains can fit together.

An efficient pattern of chain lengths need not keep producing new permutations. Repeating the pattern also permutes the symbols; when that permutation returns to its starting point, a rotation class has been repeated. A path through distinct rotation classes therefore has to interrupt the pattern. Counting the resulting losses strengthens the chain estimate. The existing reduction from words to paths then turns that estimate into a lower bound for every covering word.

The exact formula $B(n)$ uses the orders of two such permutations. Replacing those orders by a common quadratic upper bound gives a simpler formula $Q(n)$. The General submission proves

$$
S(n)\ge B(n),\qquad S(n)\ge Q(n)\qquad(n\ge8).
$$

Their complete definitions are given below and independently in [the General Challenge](../Submissions/General/Challenge.lean). The [general paper](../papers/lower/lower-bounds.pdf) develops the chain argument before deriving the formula.

## What the asymptotic submission proves

Both formulas satisfy

$$
\frac{B(n)-F_3(n)}{(n-4)!}\longrightarrow2,
\qquad
\frac{Q(n)-F_3(n)}{(n-4)!}\longrightarrow2.
$$

Consequently, for every real $\varepsilon>0$, for all sufficiently large $n$, every superpermutation on $n$ symbols has length at least $F_3(n)+(2-\varepsilon)(n-4)!$. This is an asymptotic statement about a lower bound. It does not determine the asymptotic value of $S(n)$.

For comparison, define the Fritsch–Halfar general formula by

$$
H(n)=F_3(n)+n-3+
\left\lceil\frac{2((n-2)!-(n-2))}{n^2-4n+1}\right\rceil.
$$

For either $A=B$ or $A=Q$, the following three limits hold along the indicated residue classes:

| Residue of $n$ modulo three | Asymptotic difference $A(n)-H(n)$ |
| --- | --- |
| $1$ | $(3+o(1))(n-6)!$ |
| $2$ | $(18+o(1))(n-7)!$ |
| $0$ | $(9+o(1))(n-7)!$ |

Thus both formulas exceed $H(n)$ for all sufficiently large $n$. The comparison is with the displayed general formula; Halfar’s separately searched finite bounds are different quantities.

The remaining four asymptotic claims isolate the contribution of the return orders. Let $O(n)$ be the preceding chain formula, defined below. Along $n\equiv1\pmod3$,

$$
\frac{Q(n)-O(n)}{(n-9)!}\longrightarrow\frac92,
\qquad
\liminf\frac{B(n)-O(n)}{(n-9)!}\ge\frac92.
$$

Along $n\equiv2\pmod3$,

$$
\frac{Q(n)-O(n)}{(n-11)!}\longrightarrow324,
\qquad
\liminf\frac{B(n)-O(n)}{(n-11)!}\ge324.
$$

Here each lower-limit claim means that, for every positive $\varepsilon$, the normalized difference is eventually at least the displayed constant minus $\varepsilon$. The exact-order gains need not converge to those constants: smaller return orders can give larger gains.

## The two finite submissions

The Ten submission proves $S(10)\ge4\,033\,379$, which is five more than $B(10)=4\,033\,374$. It combines a finite chain-piece certificate with the reduction to arbitrary words. The Fourteen submission proves $S(14)\ge93\,891\,141\,150$, one more than $B(14)=93\,891\,141\,149$, by ruling out equality in the preceding estimate. The [finite paper](../papers/finite/finite-lower-bounds.pdf) gives the two arguments and their provenance.

The stronger thirteen-symbol finite certificate discussed in that paper is outside the Palomar submissions. Its native-computation assumptions are not used by any selected theorem. The general result at thirteen symbols remains included.

## Precise general formulas

For parameters $p,t$, put

$$
\mathcal B_n(p,t)=F_3(n)+n-3+
\left\lceil
\frac{2(n-2)!-2(n-2)-4p/t}
 {n^2-4n+1-2(n-1)/t}
\right\rceil.
$$

The fraction is positive for every parameter choice used here. Lean uses the natural-number ceiling, which agrees with the displayed ceiling in these applications.

For $8\le n\le12$, both $B(n)$ and $Q(n)$ equal $\mathcal B_n(p,t)$ with the following parameters.

| $n$ | $p$ | $t$ |
| --- | --- | --- |
| $8$ | $10$ | $46/3$ |
| $9$ | $15$ | $287/12$ |
| $10$ | $521/80$ | $359/40$ |
| $11$ | $21$ | $263/12$ |
| $12$ | $28$ | $195/4$ |

For $n\ge13$, write $k=n-1=3m+r$, where $0\le r\le2$. The exact formula $B(n)$ uses the following parameters.

| $r$ | $p$ | $t$ |
| --- | --- | --- |
| $0$ | $2m+\tfrac12+\tfrac1{4R_0}$ | $4m-3-\tfrac1{2R_0}$ |
| $1$ | $m(2m+1)$ | $2m^2+2m-2-\tfrac1{R_1}$ |
| $2$ | $(m+1)(2m+1)$ | $4m^2+5m-\tfrac52$ |

In the first row, $R_0=2k/7$ if $7\mid k$. Otherwise, let $u$ be the unique integer with $0\le u<k$ and $7u\equiv1\pmod k$, and set $R_0=u(k-u)$. In the second row, $R_1$ is given by this table; `lcm` denotes the least common multiple of positive integers.

| $m\bmod6$ | $R_1$ |
| --- | --- |
| $0$ or $2$ | $3m+1$ |
| $1$ | $\operatorname{lcm}((2m+1)/3,(7m+2)/3)$ |
| $3$ | $\operatorname{lcm}((7m+3)/6,(11m+3)/6)$ |
| $4$ | $\operatorname{lcm}((2m+1)/3,(7m+2)/6)$ |
| $5$ | $\operatorname{lcm}((7m+1)/6,(11m+5)/6)$ |

The quadratic formula $Q(n)$ replaces both return orders by $k^2/4$. To obtain $O(n)$, keep the initial rows, replace the $r=0$ row by $(p,t)=(2m,4m-3)$, and replace the $r=1$ row by $(p,t)=(m(2m+1),2m^2+2m-2)$. The $r=2$ row is unchanged.

## Correspondence with the selected Lean statements

The four configurations select seventeen theorems. Each has a separate Challenge and Solution environment. The Asymptotics configuration contains thirteen claims, grouped below; differences between the formulas are taken in the real numbers, without truncating negative differences to zero.

| Configuration | Selected theorem names, omitting their common namespace | Mathematical claim |
| --- | --- | --- |
| General | `exact_word_bound`, `quadratic_word_bound` | The two lower bounds for all $n\ge8$ |
| Asymptotics | `exact_leading_limit`, `quadratic_leading_limit` | Leading normalized correction tends to $2$ |
| Asymptotics | `word_lower_bound_two_sub_epsilon` | Eventual word bound for every $\varepsilon>0$ |
| Asymptotics | `exact_reference_limit_zero`, `exact_reference_limit_one`, `exact_reference_limit_two` | Three comparisons of $B$ with $H$ |
| Asymptotics | `quadratic_reference_limit_zero`, `quadratic_reference_limit_one`, `quadratic_reference_limit_two` | Three comparisons of $Q$ with $H$ |
| Asymptotics | `quadratic_gain_zero_limit`, `quadratic_gain_one_limit` | Two limits for $Q-O$ |
| Asymptotics | `exact_gain_zero_asymptotic_lower`, `exact_gain_one_asymptotic_lower` | Two eventual lower estimates for $B-O$ |
| Ten | `word_lower_bound` | $S(10)\ge4\,033\,379$ |
| Fourteen | `word_lower_bound` | $S(14)\ge93\,891\,141\,150$ |

The suffixes `zero`, `one`, and `two` refer to $n-1$ modulo three, so they correspond respectively to alphabet sizes $n\equiv1,2,0\pmod3$. The complete names and statements appear in the [General](../Submissions/General/Challenge.lean), [Asymptotics](../Submissions/Asymptotics/Challenge.lean), [Ten](../Submissions/Ten/Challenge.lean), and [Fourteen](../Submissions/Fourteen/Challenge.lean) Challenges. All four configurations permit only `propext`, `Quot.sound`, and `Classical.choice`.
