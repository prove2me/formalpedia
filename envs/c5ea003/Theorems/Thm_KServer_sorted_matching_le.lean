-- Prove2me | Theorems.Thm_KServer_sorted_matching_le
-- name    : KServer.sorted_matching_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T04:16:20.472969+00:00
-- url     : https://prove2.me/theorems/88b88cc9-5ecd-4a89-8aeb-3eca4375a69a
-- title:
--   On the line, the minimum-cost matching is the sorted one
-- statement:
--   Let $x,y:\{1,\dots,k\}\to\mathbb R$ be two $k$-tuples of reals, thought of as two configurations of $k$ labelled servers on the line, and let $x^{\uparrow},y^{\uparrow}$ be their monotone rearrangements.
--
--   **Statement.** Pairing the two configurations in sorted order is at least as cheap as pairing them by their given labels:
--   $$\sum_{i=1}^{k}\bigl|x^{\uparrow}_i-y^{\uparrow}_i\bigr|\;\le\;\sum_{i=1}^{k}\bigl|x_i-y_i\bigr| .$$
--
--   Equivalently: on the real line the minimum-cost perfect matching between two $k$-point configurations is the one that matches them in sorted order, and sorting is a contraction for the $\ell^1$ distance.
--
--   **Role.** This is the geometric fact that every potential-function analysis of a $k$-server algorithm on the line rests on. Such an analysis carries a potential of the form $k\cdot(\text{matching cost between the algorithm's servers and the adversary's})+(\text{spread of the algorithm's servers})$, and needs two things from the matching term: that an adversary move of length $t$ raises it by at most $t$, and that the sorted matching may be used when reasoning about which of the algorithm's servers moves toward which of the adversary's. Both are this statement. It is also what licenses the standard simplification "assume the adversary keeps its servers in sorted order", since re-sorting a schedule never increases its cost.
--
--   **Formalization Note** `Tuple.sort f` is Mathlib's permutation making `f ∘ Tuple.sort f` monotone, so `x ∘ Tuple.sort x` is the monotone rearrangement of `x`. Both sides are sums over `Fin k`; no hypothesis on $k$ is needed, the case $k=0$ being the empty sum.
-- source:
--   Chrobak--Karloff--Payne--Vishwanathan, New results on server problems, SIAM J. Discrete Math. 4 (1991) 172-181, https://doi.org/10.1137/0404017 -- the geometric fact underlying the potential-function analysis of Double Coverage on the real line (the matching term of the potential is taken between the sorted configurations). See also E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, Section 3.2.

import Mathlib

namespace KServer

theorem sorted_matching_le (k : ℕ) (x y : Fin k → ℝ) :
    ∑ i, |(x ∘ Tuple.sort x) i - (y ∘ Tuple.sort y) i| ≤ ∑ i, |x i - y i| := by sorry

end KServer
