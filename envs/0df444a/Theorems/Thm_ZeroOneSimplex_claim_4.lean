-- Prove2me | Theorems.Thm_ZeroOneSimplex_claim_4
-- name    : ZeroOneSimplex.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:44.563832+00:00
-- url     : https://prove2.me/theorems/e2215b0d-be3a-4b66-ac7b-ab77c316ccc0
-- title:
--   Claim 4 — slope comparison as a polynomial inequality in $c^*$
-- statement:
--   Consider a 0/1-LP of form (1) with feasible region $P$, an initial vertex $x^0$ and the Ordered Shadow vector $v(k)=(-1)^{x^0(k)}(c^*)^k$. Let $x$ be a point of $P$ and $u^0,u^1$ neighbors of $x$ that are both $c$-improving and $v$-improving. Let $b=\max\{f(u^0),f(u^1)\}$, assume $f(x)\le b$, and let
--   $$
--   \kappa_j=\sigma_j\big[c^\top(u^0-x)(u^1(j)-x(j))-c^\top(u^1-x)(u^0(j)-x(j))\big],\qquad \sigma_j=(-1)^{x^0(j)}.
--   $$
--   Then
--   $$
--   \frac{c^\top(u^0-x)}{v^\top(u^0-x)}>\frac{c^\top(u^1-x)}{v^\top(u^1-x)}
--   \quad\Longleftrightarrow\quad
--   \kappa_b(c^*)^b>\sum_{j=1}^{b-1}-\kappa_j(c^*)^j .
--   $$
--
--   Claim 4 turns the comparison of slopes made by the Ordered Shadow rule into a statement about the leading coefficient of a polynomial in $c^*$.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - encoding: P a 0/1 polytope → P nonempty and bounded with every extreme point in {0,1}ⁿ (IsZeroOneLP); reason: P is a compact convex set, so it is the convex hull of its extreme points; an empty P has no vertex and no basis
--   - generalization: c, b, d, A and D integral (p.2) → c integral; A, b, D, d real; reason: integrality of A, b, D, d is never used; integral data are a special case
--   - generalization: A of full row rank (assumption (i), p.6) → not assumed; reason: the statement concerns the feasible region P and no basis; full-rank instances are a special case
--   - encoding: coordinates k = 1, …, n → coordinates Fin n, the paper's coordinate k being k.val + 1 (exponents of c*, f and κ are 1-based); reason: Lean indexing; the same vectors and the same values of f
--   - generalization: x⁰ = 0 after a change of coordinates (p.19), v = ((c*), (c*)², …, (c*)ⁿ) → x⁰ any vertex, v(k) = (−1)^{x⁰(k)}(c*)^k of Definition 5; reason: for x⁰ = 0 this is the printed statement; the change of coordinates is avoided
--   - generalization: the standing context of the proof of Theorem 6 (p.19): xⁱ is the c-maximum of F_{f(xⁱ)}, so every c-improving neighbor has larger f → only f(x) ≤ b is assumed; reason: the context implies f(x) < f(u⁰), f(u¹), hence f(x) ≤ b
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Claim 4, pp.19–20 (in the proof of Theorem 6)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Claim 4** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, pp.19–20, in the proof of
Theorem 6). Consider a 0/1-LP of the form (1) with feasible region `P`, an initial vertex `x⁰`,
and the vector `v` of Definition 5. Let `u⁰, u¹` be neighbors of a vertex `x` of `P` that are both
`c`-improving and `v`-improving, let `b = max{f(u⁰), f(u¹)}`, assume `f(x) ≤ b`, and let `κ_j` be
as in `kappa`. Then
`cᵀ(u⁰ − x)/vᵀ(u⁰ − x) > cᵀ(u¹ − x)/vᵀ(u¹ − x)` if and only if
`κ_b (c*)^b > Σ_{j=1}^{b−1} −κ_j (c*)^j`.

**Formalization Note.** The paper proves the claims after the change of coordinates `x⁰ = 0`
and under the standing context of the proof of Theorem 6 (`x` is the `c`-maximum of
`F_{f(x)}`, so `f(x) < f(u)` for `c`-improving neighbors `u`). Here `x⁰` is arbitrary, the sign
`σ_j = (−1)^{x⁰(j)}` is a factor of `κ_j`, and only `f(x) ≤ b` is assumed. -/
theorem claim_4 {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ Set.extremePoints ℝ L.feasibleRegion) (x u0 u1 : Fin n → ℝ)
    (hu0 : IsEdge L.feasibleRegion x u0) (hu1 : IsEdge L.feasibleRegion x u1)
    (hc0 : L.c ⬝ᵥ x < L.c ⬝ᵥ u0) (hc1 : L.c ⬝ᵥ x < L.c ⬝ᵥ u1)
    (hv0 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u0)
    (hv1 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u1)
    (hfx : fIndex x0 x ≤ max (fIndex x0 u0) (fIndex x0 u1)) :
    (L.c ⬝ᵥ (u1 - x) / L.orderedShadowVec x0 ⬝ᵥ (u1 - x) <
        L.c ⬝ᵥ (u0 - x) / L.orderedShadowVec x0 ⬝ᵥ (u0 - x)) ↔
      ∑ j ∈ Finset.Ico 1 (max (fIndex x0 u0) (fIndex x0 u1)),
          -kappa L.c x0 x u0 u1 j * L.cStar ^ j <
        kappa L.c x0 x u0 u1 (max (fIndex x0 u0) (fIndex x0 u1)) *
          L.cStar ^ (max (fIndex x0 u0) (fIndex x0 u1)) := by sorry

end ZeroOneSimplex
