-- Prove2me | Theorems.Thm_ZeroOneSimplex_lemma_6
-- name    : ZeroOneSimplex.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:46.530207+00:00
-- url     : https://prove2.me/theorems/8f1ec9b3-9c96-4054-8d06-f5adde9a2a09
-- title:
--   Lemma 6 — degenerate pivots reach a basis with the slope condition
-- statement:
--   Given an LP of form (1) with real data, not necessarily a 0/1-LP, with feasible region $Q$ ($A$ of full row rank), let $B^0$ be a feasible basis of its standard form with vertex $x^0$, and let $v$ be defined according to a Shadow rule: $x^0$ is a $c$-maximum of the $v$-minimal face of $Q$. Then there is a finite sequence of degenerate pivots $B^0=B_0\to B_1\to\dots\to B_T$ such that $B_T$ satisfies: for each $z\in\mathcal C(B_T)$, $c^\top z>0$ implies $v^\top z>0$.
--
--   This supplies the starting basis of Theorem 7.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - generalization: c, b, d, A and D integral (p.2) → c, A, b, D, d all real; reason: §3.4 treats a general LP (p.22), and the generic objective of p.25 is a random perturbation of c, so it is not integral; integrality is used only in Claims 2 and 3; integral data are a special case
--   - encoding: pivot direction z′ʲ(B) = A′_B⁻¹A′_j (pp.7, 11) → the unique w with A′w = 0, w_j = 1, w_k = 0 for nonbasic k ≠ j; reason: the printed formula has the wrong sign (the direction must satisfy A′w = 0); the ratio test (2) is unchanged
--   - generalization: B⁰ not optimal and not satisfying the condition → no such hypotheses; reason: if B⁰ satisfies the condition the empty sequence works; optimality of B⁰ plays no role in the statement
--   - reading: v defined according to a given Shadow rule → x⁰ is a c-maximum of the v-minimal face of Q; reason: Definition 3, p.13: x⁰ is the c-maximum of the v-minimal face of π(Q)
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Lemma 6, p.24

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_IsPivot
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Lemma 6** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.24). Given an LP of the
form (1) with feasible region `Q`, let `B⁰` be an initial feasible basis of its standard equality
form, with vertex `x⁰`, and let `v` be defined according to a Shadow rule: `x⁰` is the
`c`-maximum of the `v`-minimal face of `Q`. Then there is a finite sequence of degenerate pivots
from `B⁰` to a basis `B` satisfying: for each `z ∈ 𝒞(B)`, if `cᵀz > 0` then `vᵀz > 0`.

**Formalization Note.** The LP is general (§3.4, p.22): all its data, `c` included, are real.
The paper assumes in addition that `B⁰` is not optimal and does not
satisfy the condition; the statement here drops both (when `B⁰` satisfies the condition the
empty sequence works). -/
theorem lemma_6 {n m p : ℕ} (L : LPData n m p) (hA : L.A.rank = m)
    (B0 : Finset (Fin n ⊕ Fin p)) (hB0 : L.IsFeasibleBasis B0) (v : Fin n → ℝ)
    (hv : IsMaximizer (vMinFace L.feasibleRegion v) L.c (L.vertexOf B0)) :
    ∃ (T : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p)), B 0 = B0 ∧
      (∀ t < T, L.IsDegeneratePivot (B t) (B (t + 1))) ∧ L.IsReady (B T) v := by sorry

end ZeroOneSimplex
