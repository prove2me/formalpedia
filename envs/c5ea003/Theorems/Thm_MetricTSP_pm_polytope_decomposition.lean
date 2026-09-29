-- Prove2me | Theorems.Thm_MetricTSP_pm_polytope_decomposition
-- name    : MetricTSP.pm_polytope_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-25T05:09:28.129553+00:00
-- url     : https://prove2.me/theorems/0c49da61-535d-4a47-a8f4-c60f11811714
-- title:
--   Edmonds' perfect matching polytope theorem, convex decomposition form
-- statement:
--   **Edmonds' perfect matching polytope theorem**, in explicit convex-decomposition form. Let $W$ be an even-cardinality vertex set and $y$ a point of the perfect matching polytope on $W$: symmetric, nonnegative, zero diagonal, supported inside $W$, with degree $\sum_u y(v,u)=1$ at every $v \in W$ and with $y(\delta(S)) \ge 1$ for every odd-cardinality $S \subseteq W$. Then $y$ is a finite convex combination of perfect matchings of $W$: there is a nonempty list of pairs $(\lambda_i, f_i)$ with $\lambda_i > 0$, $\sum_i \lambda_i = 1$, each $f_i$ a fixed-point-free involution of $W$ (identity off $W$), and
--   $$y(u,v) \;=\; \sum_{i\,:\,f_i(u)=v,\ u \in W} \lambda_i \qquad \text{for all } u,v.$$
--
--   The classical proof is by induction on $(|W|, |\mathrm{supp}\,y|)$. If some entry equals $1$, that pair can be stripped and the rest decomposed on $W$ minus two vertices. If some **nontrivial tight odd cut** $y(\delta(S)) = 1$ ($3 \le |S| \le |W|-3$) exists, both sides are contracted to single representative vertices; the two decompositions obtained inductively are glued with weights $\lambda_i \mu_j\, y(a_i,b_j) / (\alpha(a_i)\beta(b_j))$, where $a_i, b_j$ are the representatives' partners and $\alpha, \beta$ the cross-mass marginals — the cross-edges of $y$ itself provide exactly the coupling needed to reproduce $y$. Otherwise every entry is strictly fractional and no nontrivial odd cut is tight; a balanced nonzero perturbation supported on the support of $y$ (`MetricTSP.support_perturbation`) can be pushed to its feasibility limits in both directions, writing $y$ as a convex combination of two feasible points each of which loses a support edge, gains a unit entry, or gains a nontrivial tight odd cut — all cases with smaller induction measure.
--
--   Via `MetricTSP.even_set_matching`, this supplies the parity-correction matching of Wolsey's $\tfrac32$ analysis of the Held–Karp relaxation.
-- source:
--   J. Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B (1965) 125-130; A. Schrijver, Combinatorial Optimization: Polyhedra and Efficiency, Springer 2003, Theorem 25.1.

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem pm_polytope_decomposition (n : ℕ) (W : Finset (Fin n)) (hW : Even W.card)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hodd : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ L : List (ℝ × (Fin n → Fin n)), L ≠ [] ∧
      (∀ p ∈ L, 0 < p.1 ∧
        (∀ v ∈ W, p.2 v ∈ W ∧ p.2 (p.2 v) = v ∧ p.2 v ≠ v) ∧
        (∀ v ∉ W, p.2 v = v)) ∧
      (L.map Prod.fst).sum = 1 ∧
      (∀ u v, y u v
        = (L.map (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0)).sum) := by sorry

end MetricTSP
