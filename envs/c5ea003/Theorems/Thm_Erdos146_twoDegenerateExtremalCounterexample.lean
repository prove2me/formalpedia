-- Prove2me | Theorems.Thm_Erdos146_twoDegenerateExtremalCounterexample
-- name    : Erdos146.twoDegenerateExtremalCounterexample
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:54:43.587288+00:00
-- url     : https://prove2.me/theorems/371110e6-9b73-41d4-88c4-5aa470d746d6
-- title:
--   Failure of the 2-degenerate extremal bound (Theorem 1.2)
-- statement:
--   **Theorem 1.2 (Failure of the 2-degenerate bound).** There exist a fixed connected bipartite 2-degenerate graph $H$ and constants $c, \varepsilon > 0$ such that
--
--   $$\mathrm{ex}(n, H) \ \ge\ c\, n^{3/2 + \varepsilon}$$
--
--   for all sufficiently large $n$.
--
--   A graph $H$ is **$r$-degenerate** if every nonempty subgraph of $H$ has a vertex of degree at most $r$. Erdős conjectured (Erdős problem #146) that every fixed bipartite $r$-degenerate graph $H$ satisfies $\mathrm{ex}(n,H) = O(n^{2-1/r})$. Chapter 10 of the source disproves this for $r = 2$. Since the conjectured bound for $r = 2$ is $\mathrm{ex}(n,H) = O(n^{3/2})$, a polynomial excess $n^{\varepsilon}$ refutes it outright. The counterexample graph $H$ is built in layers (Section 6): starting from a layer $V_0$ of size $L_0$, each subsequent layer is $V_i = \binom{V_{i-1}}{2}$, and every vertex $\{a,b\} \in V_i$ is joined to its two parents $a, b \in V_{i-1}$. Fact 6.1 records that the result is connected, bipartite and 2-degenerate. The lower bound comes from the host is the sampled hamming-ball graph of section 7: with $u = \{0,1\}^m$, two disjoint copies $u_l, u_r$ are joined whenever their hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. A second-moment argument shows the sampled graph has $\Omega(n^{3/2+\varepsilon})$ edges, Proposition 8.1 shows it is $H$-free with probability $1 - o(1)$, and padding extends the construction to every sufficiently large order.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18440-L18541

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem Erdos146.twoDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsTwoDegenerate H ∧
      (∀ coloring : H.Coloring (Fin 2), ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin q => coloring vertex = side)).sup
          (fun vertex => H.degree vertex)) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by sorry
