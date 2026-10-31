-- Prove2me | Theorems.Thm_ZeroOneSimplex_claim_1
-- name    : ZeroOneSimplex.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:50.687095+00:00
-- url     : https://prove2.me/theorems/68a4a09e-e0f3-4138-aab6-92c26c31d370
-- title:
--   Claim 1 — $c$-improving neighbors are $v$-improving
-- statement:
--   Consider a 0/1-LP of form (1) with feasible region $P$, an initial vertex $x^0$ and the Ordered Shadow vector $v$. Let $x$ be a $c$-maximum of the face $F_{f(x)}=\{y\in P: f(y)\le f(x)\}$. If $u$ is a $c$-improving neighbor of $x$, then $u$ is also $v$-improving:
--   $$
--   v^\top x<v^\top u .
--   $$
--
--   So the Ordered Shadow rule, which looks only at $v$-improving neighbors, never misses a $c$-improving one.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - encoding: P a 0/1 polytope → P nonempty and bounded with every extreme point in {0,1}ⁿ (IsZeroOneLP); reason: P is a compact convex set, so it is the convex hull of its extreme points; an empty P has no vertex and no basis
--   - generalization: c, b, d, A and D integral (p.2) → c integral; A, b, D, d real; reason: integrality of A, b, D, d is never used; integral data are a special case
--   - generalization: A of full row rank (assumption (i), p.6) → not assumed; reason: the statement concerns the feasible region P and no basis; full-rank instances are a special case
--   - encoding: coordinates k = 1, …, n → coordinates Fin n, the paper's coordinate k being k.val + 1 (exponents of c*, f and κ are 1-based); reason: Lean indexing; the same vectors and the same values of f
--   - generalization: x⁰ = 0 after a change of coordinates (p.19), v = ((c*), (c*)², …, (c*)ⁿ) → x⁰ any vertex, v(k) = (−1)^{x⁰(k)}(c*)^k of Definition 5; reason: for x⁰ = 0 this is the printed statement; the change of coordinates is avoided
--   - generalization: the claim is stated for the vertex xⁱ of the path under the standing context of the proof of Theorem 6 (p.19): xⁱ is the c-maximum of F_{f(xⁱ)}, so every c-improving neighbor has larger f → x is any point that is a c-maximum of F_{f(x)} (hypothesis hx); reason: the inductive context of p.19 made an explicit hypothesis; every path vertex satisfies it, and it is the only property of xⁱ the proof uses
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Claim 1, p.19 (in the proof of Theorem 6; proved p.21)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Claim 1** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.19, in the proof of
Theorem 6). Consider a 0/1-LP of the form (1) with feasible region `P`, an initial vertex `x⁰`,
and the vector `v` of Definition 5. Let `x` be a vertex of the path that is a `c`-maximum of the
face `F_{f(x)} = {y ∈ P : f(y) ≤ f(x)}`. If `u` is a `c`-improving neighbor of `x`, then `u` is
also `v`-improving.

**Formalization Note.** The standing context of the claim (p.19: "we are able to assume that
`xⁱ` is the `c`-maximum of the face `F_{f(xⁱ)}`") is the hypothesis `hx`. No change of
coordinates `x⁰ = 0` is made; `x⁰` is any vertex. -/
theorem claim_1 {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ Set.extremePoints ℝ L.feasibleRegion) (x u : Fin n → ℝ)
    (hx : IsMaximizer {y | y ∈ L.feasibleRegion ∧ fIndex x0 y ≤ fIndex x0 x} L.c x)
    (hu : IsEdge L.feasibleRegion x u) (hcu : L.c ⬝ᵥ x < L.c ⬝ᵥ u) :
    L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u := by sorry

end ZeroOneSimplex
