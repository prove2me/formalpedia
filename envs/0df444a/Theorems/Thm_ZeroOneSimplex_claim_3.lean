-- Prove2me | Theorems.Thm_ZeroOneSimplex_claim_3
-- name    : ZeroOneSimplex.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:37.276405+00:00
-- url     : https://prove2.me/theorems/3fe15da4-1e53-4d93-abd9-0f5984d48648
-- title:
--   Claim 3 — among equal $f$, larger $c$-value has larger slope
-- statement:
--   Consider a 0/1-LP of form (1) with integral objective $c$, feasible region $P$, an initial vertex $x^0$ and the Ordered Shadow vector $v(k)=(-1)^{x^0(k)}(c^*)^k$, $c^*=\|c\|_1+2$. Let $u^0,u^1$ be neighbors of a point $x$ of $P$ that are both $c$-improving and $v$-improving. Suppose $b=f(u^1)=f(u^0)$, $f(x)<b$ and $c^\top u^0>c^\top u^1$. Then
--   $$
--   \frac{c^\top(u^0-x)}{v^\top(u^0-x)}>\frac{c^\top(u^1-x)}{v^\top(u^1-x)} .
--   $$
--
--   Together with Claim 2 and Claim 1 this shows that the Ordered Shadow rule picks a $c$-best $f$-minimal improving neighbor, i.e. follows a Lemma 5 path.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - encoding: P a 0/1 polytope → P nonempty and bounded with every extreme point in {0,1}ⁿ (IsZeroOneLP); reason: P is a compact convex set, so it is the convex hull of its extreme points; an empty P has no vertex and no basis
--   - generalization: c, b, d, A and D integral (p.2) → c integral; A, b, D, d real; reason: integrality of A, b, D, d is never used; integral data are a special case
--   - generalization: A of full row rank (assumption (i), p.6) → not assumed; reason: the statement concerns the feasible region P and no basis; full-rank instances are a special case
--   - encoding: coordinates k = 1, …, n → coordinates Fin n, the paper's coordinate k being k.val + 1 (exponents of c*, f and κ are 1-based); reason: Lean indexing; the same vectors and the same values of f
--   - generalization: x⁰ = 0 after a change of coordinates (p.19), v = ((c*), (c*)², …, (c*)ⁿ) → x⁰ any vertex, v(k) = (−1)^{x⁰(k)}(c*)^k of Definition 5; reason: for x⁰ = 0 this is the printed statement; the change of coordinates is avoided
--   - generalization: the standing context of the proof of Theorem 6 (p.19): xⁱ is the c-maximum of F_{f(xⁱ)}, so every c-improving neighbor has larger f → only f(x) < b is assumed; reason: the context implies f(x) < f(u⁰), f(u¹) ≤ b
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Claim 3, p.19 (in the proof of Theorem 6; proved pp.21–22)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Claim 3** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.19, in the proof of
Theorem 6; proved pp.21–22). Consider a 0/1-LP of the form (1) with integral objective `c`,
feasible region `P`, an initial vertex `x⁰`, and the vector `v` of Definition 5. Let `u⁰, u¹` be
neighbors of a vertex `x` of `P` that are both `c`-improving and `v`-improving.
Suppose that `b = f(u¹) = f(u⁰)` and `cᵀu⁰ > cᵀu¹`. Then
`cᵀ(u⁰ − x)/vᵀ(u⁰ − x) > cᵀ(u¹ − x)/vᵀ(u¹ − x)`.

**Formalization Note.** The paper proves the claim after the change of coordinates `x⁰ = 0` and
under the standing context of the proof of Theorem 6 (`x` is the `c`-maximum of `F_{f(x)}`, so
every `c`-improving neighbor has larger `f`). Here `x⁰` is any vertex and only `f(x) < b` is
assumed (hypothesis `hfx`). -/
theorem claim_3 {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ Set.extremePoints ℝ L.feasibleRegion) (x u0 u1 : Fin n → ℝ)
    (hu0 : IsEdge L.feasibleRegion x u0) (hu1 : IsEdge L.feasibleRegion x u1)
    (hc0 : L.c ⬝ᵥ x < L.c ⬝ᵥ u0) (hc1 : L.c ⬝ᵥ x < L.c ⬝ᵥ u1)
    (hv0 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u0)
    (hv1 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u1)
    (hf : fIndex x0 u0 = fIndex x0 u1) (hfx : fIndex x0 x < fIndex x0 u1)
    (hcc : L.c ⬝ᵥ u1 < L.c ⬝ᵥ u0) :
    L.c ⬝ᵥ (u1 - x) / L.orderedShadowVec x0 ⬝ᵥ (u1 - x) <
      L.c ⬝ᵥ (u0 - x) / L.orderedShadowVec x0 ⬝ᵥ (u0 - x) := by sorry

end ZeroOneSimplex
