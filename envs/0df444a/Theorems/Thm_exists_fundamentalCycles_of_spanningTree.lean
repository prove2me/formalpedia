-- Prove2me | Theorems.Thm_exists_fundamentalCycles_of_spanningTree
-- name    : exists_fundamentalCycles_of_spanningTree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/caaa9d3e-3280-50bb-897c-455b7ebf656e
-- title:
--   Fundamental cycles of a spanning tree generate all flows
-- statement:
--   Let $V$ and $E$ be finite types with decidable equality, and let $hd, tl : E \to V$ be two maps, to be read as the head and tail of each edge of a finite directed multigraph, so that $e$ runs from $tl\,e$ to $hd\,e$. Let $T$ be a finite set of edges, and assume the spanning-tree hypothesis in the following form: for every pair of vertices $u, v$ there is exactly one $c : E \to \mathbb{Z}$ supported on $T$ (that is, $c\,e = 0$ for all $e \notin T$) whose divergence at each vertex $w$, namely $\sum_{e : hd\,e = w} c\,e - \sum_{e : tl\,e = w} c\,e$, equals $[w = v] - [w = u]$. The conclusion asserts the existence of $Z : E \to E \to \mathbb{Z}$ such that: (i) for every index $j$, the chain $Z\,j$ is a circulation, i.e. $\sum_{e : hd\,e = w} Z\,j\,e = \sum_{e : tl\,e = w} Z\,j\,e$ at every vertex $w$; (ii) for $j, j'$ in the complement $T^{c}$ one has $Z\,j\,j' = 1$ if $j = j'$ and $0$ otherwise; (iii) $Z\,j = 0$ for $j \in T$; and (iv) for every additive commutative group $A$ and every $f : E \to A$ satisfying the balance condition $\sum_{e : hd\,e = w} f\,e = \sum_{e : tl\,e = w} f\,e$ at every vertex $w$, one has $f\,e = \sum_{j \in T^{c}} Z\,j\,e \cdot f\,j$ for every edge $e$, the coefficients acting through the $\mathbb{Z}$-module structure of $A$.
--
--   This is the classical statement that the fundamental cycles attached to the edges outside a spanning tree span the cycle space of a finite directed multigraph, here formulated for flows with values in an arbitrary abelian group: such a flow is determined, with universal integer coefficients, by its values on the non-tree edges. It is used in the construction of path integrals on curves, in [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw) and in [`CerednikDrinfeld.Omega.exists_isUnit_det_pathCycle_and_span_pathCycle`](thm.html#CerednikDrinfeld.Omega.exists_isUnit_det_pathCycle_and_span_pathCycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_fundamentalCycles_of_spanningTree.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem exists_fundamentalCycles_of_spanningTree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (hd tl : E → V) (T : Finset E)
    (hTpath : ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ Z : E → E → ℤ,
      (∀ j, ∀ w, (∑ e with hd e = w, Z j e) = (∑ e with tl e = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {A : Type*} [inst : AddCommGroup A] (f : E → A),
        (∀ w, (∑ e with hd e = w, f e) = (∑ e with tl e = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by sorry
