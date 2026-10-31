-- Prove2me | Theorems.Thm_ZeroOneSimplex_theorem_7
-- name    : ZeroOneSimplex.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:48.839506+00:00
-- url     : https://prove2.me/theorems/9063b799-6029-4559-9aad-6068bffde0b9
-- title:
--   Theorem 7 — from a basis with the slope condition, the simplex method follows the Shadow rule
-- statement:
--   Given an LP of form (1) with real data, not necessarily a 0/1-LP, with feasible region $Q$ ($A$ of full row rank), let $B_0$ be a feasible basis of its standard form and $v$ an auxiliary vector such that for each $z\in\mathcal C(B_0)$, $c^\top z>0$ implies $v^\top z>0$. Run the simplex method from $B_0$, entering at each basis an improving pivot direction $z\in\mathcal C(B)$ that maximizes $c^\top z/v^\top z$ (any leaving variable allowed by the ratio test). Then
--
--   1. every basis $B_t$ visited satisfies the same condition; and
--   2. at every non-degenerate pivot $B_t\to B_{t+1}$ the new vertex is a Shadow rule step for $(c,v)$ from the old one.
--
--   So the simplex method follows the same path on the 1-skeleton of $Q$ as the Shadow rule.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - generalization: c, b, d, A and D integral (p.2) → c, A, b, D, d all real; reason: §3.4 treats a general LP (p.22), and the generic objective of p.25 is a random perturbation of c, so it is not integral; integrality is used only in Claims 2 and 3; integral data are a special case
--   - encoding: pivot direction z′ʲ(B) = A′_B⁻¹A′_j (pp.7, 11) → the unique w with A′w = 0, w_j = 1, w_k = 0 for nonbasic k ≠ j; reason: the printed formula has the wrong sign (the direction must satisfy A′w = 0); the ratio test (2) is unchanged
--   - generalization: v defined according to a given Shadow rule (x⁰ the c-maximum of the v-minimal face) → any v; reason: the proof uses only the slope condition at B₀
--   - reading: follows the same path as the one followed by the Shadow rule → every non-degenerate pivot is a Shadow rule step (adjacent, v-improving, largest slope), and the slope condition persists; reason: the Shadow rule's argmax may have ties (p.13), so the path is one the rule may follow
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Theorem 7, p.23

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData_IsPivot
import Definitions.Def_ZeroOneSimplex_IsShadowPath
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Theorem 7** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.23). Given an LP of the
form (1) with feasible region `Q`, let `B 0` be an initial feasible basis of its standard equality
form and `v` an auxiliary vector, and assume that for each `z ∈ 𝒞(B 0)`, if `cᵀz > 0` then
`vᵀz > 0`. Start from `B 0` and at each basis pivot on an improving pivot direction
`z ∈ 𝒞(B)` that maximizes `cᵀz / vᵀz` (with any leaving variable allowed by the ratio test).
Then the simplex method follows the same path on the 1-skeleton of `Q` as the Shadow rule:
1. every basis `B t` visited satisfies the same condition; and
2. at every non-degenerate pivot `B t → B (t+1)` the new vertex is a Shadow rule step from the
   old one for `(c, v)` (adjacent, `v`-improving, of largest slope).

**Formalization Note.** The LP is general (§3.4, p.22): all its data, `c` included, are real, and
it need not be a 0/1-LP. The paper takes `v` "defined according to a given Shadow rule"; the
statement here holds for every `v`. Ties of the Shadow rule's argmax are allowed (p.13), so "the
same path" means a path the Shadow rule may follow. -/
theorem theorem_7 {n m p : ℕ} (L : LPData n m p) (hA : L.A.rank = m) (v : Fin n → ℝ)
    (B : ℕ → Finset (Fin n ⊕ Fin p)) (T : ℕ) (hB0 : L.IsFeasibleBasis (B 0))
    (hready : L.IsReady (B 0) v)
    (hstep : ∀ t < T, ∃ j ℓ, L.IsPivot (B t) (B (t + 1)) j ℓ ∧ L.IsShadowEntering (B t) v j) :
    (∀ t ≤ T, L.IsReady (B t) v) ∧
      ∀ t < T, L.vertexOf (B (t + 1)) ≠ L.vertexOf (B t) →
        IsShadowStep L.feasibleRegion L.c v
          (L.vertexOf (B t)) (L.vertexOf (B (t + 1))) := by sorry

end ZeroOneSimplex
