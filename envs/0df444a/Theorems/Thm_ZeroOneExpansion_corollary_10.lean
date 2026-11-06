-- Prove2me | Theorems.Thm_ZeroOneExpansion_corollary_10
-- name    : ZeroOneExpansion.corollary_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:17.18195+00:00
-- url     : https://prove2.me/theorems/1622d594-67df-42ba-831f-bd44b9af71e3
-- title:
--   Corollary 10 — cross-layer edges of $P_n$
-- statement:
--   Let $n\ge1$, $u=(u_1,\dots,u_{2n})\in X_n$ and $v=(v_1,\dots,v_{2n})\in Y_n$. Then $[(u,0),(v,1)]$ is an edge of $P_n$ if and only if, for every $i\in[n]$,
--   $$(u_i,v_i)\in\mathcal R\quad\text{and}\quad (v_{n+i},u_{n+i})\in\mathcal R.$$
--   In the second group the order is reversed, because there the blocks of $X_n$ lie in $D$ and those of $Y_n$ in $C$.
--
--   Differences from the source:
--   - encoding: "[u, v] is an edge" (a one-dimensional face) → the segment [u, v] is a face (IsExposed ℝ P (segment ℝ u v)); reason: the two endpoints are distinct, so the segment is one-dimensional, and a one-dimensional face is an edge
--   - encoding: blocks 1, …, 2n and [n] = {1, …, n} → blocks indexed by Fin n ⊕ Fin n (first group inl, second group inr), [n] as Fin n (0-based); block k at coordinates 2k−2, 2k−1, t last; reason: a relabelling; same instances
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Corollary 10, p.6

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_compatR

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Corollary 10** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.6). Let `u = (u_1, …, u_{2n}) ∈ Xn` and `v = (v_1, …, v_{2n}) ∈ Yn`.
Then `[(u, 0), (v, 1)]` is an edge of `Pn` iff `(u_i, v_i) ∈ R` and `(v_{n+i}, u_{n+i}) ∈ R` for
every `i ∈ [n]`.

**Formalization Note** §3 fixes `n ≥ 1`. `(u, 0)` is `withLast u 0`. First-group block `i` is
`blk n u (Sum.inl i)` (the paper's `u_i`) and second-group block `i` is `blk n u (Sum.inr i)` (the
paper's `u_{n+i}`); `[n]` is `Fin n`. Note the order in the second group: `(v_{n+i}, u_{n+i}) ∈ R ⊆ C × D`.
"Is an edge" is "is a face" (`IsExposed`), as in Fact 6. -/
theorem corollary_10 (n : ℕ) (hn : 1 ≤ n) (u v : Fin (4 * n) → ℝ) (hu : u ∈ Xn n)
    (hv : v ∈ Yn n) :
    IsExposed ℝ (Pn n) (segment ℝ (withLast u 0) (withLast v 1)) ↔
      ∀ i : Fin n, (blk n u (Sum.inl i), blk n v (Sum.inl i)) ∈ compatR ∧
        (blk n v (Sum.inr i), blk n u (Sum.inr i)) ∈ compatR := by sorry

end ZeroOneExpansion
