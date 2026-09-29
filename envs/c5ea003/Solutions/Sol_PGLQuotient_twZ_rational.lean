-- Prove2me | solution 1 for PGLQuotient.twZ_rational
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:44:47.58511+00:00
-- url     : https://prove2.me/submissions/6fb1788b-dbe1-42df-b75f-3df12b6f47ad

-- Sol generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra
import Theorems.Thm_PGLQuotient_twMass_eq
import Theorems.Thm_PGLQuotient_twZMass_succ

/-!
# The height zeta function in arbitrary rank: rationality and the pole at `s = d`

`Algebra.PGLQuotient.HeightZetaRankTwo` computes the positive-moment height zeta function

`Z_d(s) = ∑_λ α(λ)^s / |Aut λ|`

of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in closed form for `d = 2`,
exhibiting it as a rational function of `u = q^{s/2}` with a single pole at `u = q`.
This file establishes the corresponding statement in **arbitrary rank `d ≥ 1`**.

The mechanism is the same row-peeling recursion that produced the vertex volume in
`Algebra.PGLQuotient.VertexVolumeGeneral`, run on a *height-weighted* twisted mass

`twZ q c j w λ = w ^ heightExp λ · twWeight q c j λ`.

Since `heightExp (cons a λ') = (n+1)·a + heightExp λ'`, the extra factor is compatible with
peeling: it only changes the ratio of the geometric series in the top gap from
`q^{-(n+1)(c+1)}` to `w^{n+1} q^{-(n+1)(c+1)}`.  Hence:

* `twZMass_succ` — the row-peeling recursion for the height-weighted twisted mass;
* `twZ_rational` — for every rank and every pair of twisting parameters the sum is a rational
  function of `w` on the whole interval `0 ≤ w < q`, with a denominator that does not vanish
  there;
* `heightZeta_rational_general` — **the height zeta function of the rank-`d` quotient is a
  rational function of `u = q^{s/d}`**, uniformly for `s < d`;
* `heightZeta_unbounded_general` — **the pole at `s = d` is genuine in every rank**:
  `Z_d(s) → ∞` as `s ↑ d`.  Combined with `summable_weight_height_iff` this pins the abscissa
  of convergence at exactly `s = d`.

The threshold `w < q` is exactly `s < d` under `w = q^{s/d}`, so the domain of rationality is
precisely the half-plane of convergence.
-/

open PGLQuotient

open Finset

variable {q : ℝ}




variable {d : ℕ}







variable {w : ℝ}







open Polynomial








open PGLQuotient in
theorem solution(hq : 1 < q) (n c j : ℕ) :
    ∃ P Q : Polynomial ℝ, ∀ w : ℝ, 0 ≤ w → w < q →
      Q.eval w ≠ 0 ∧ ∑' g : Vertex (n + 1), twZ q c j w g = P.eval w / Q.eval w := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  induction n generalizing c j with
  | zero =>
      refine ⟨C ((q ^ (1 + j) - 1)⁻¹), 1, fun w hw hwq => ⟨by simp, ?_⟩⟩
      have hval : ∀ g : Vertex 1, twZ q c j w g = (q ^ (1 + j) - 1)⁻¹ := by
        intro g
        have hzero : heightExp g = 0 := by
          show ∑ k ∈ range 0, (0 - k) * gapAt g k = 0
          simp
        unfold twZ
        rw [hzero, pow_zero, one_mul]
        have := twMass_eq (q := q) hq 0 c j
        have hsub : ∀ b : Vertex 1, b = (fun i => i.elim0) := fun b => funext (fun i => i.elim0)
        have hg : g = (fun i => i.elim0) := hsub g
        subst hg
        rw [tsum_eq_single (fun i => i.elim0) (fun b hb => absurd (hsub b) hb)] at this
        rw [this]
        unfold NumV DenV
        simp [Gpoly, Jfac, Pfac, Cfac]
      rw [tsum_congr hval]
      have hsub : ∀ b : Vertex 1, b = (fun i => i.elim0) := fun b => funext (fun i => i.elim0)
      rw [tsum_eq_single (fun i => i.elim0) (fun b hb => absurd (hsub b) hb)]
      simp
  | succ m ih =>
      obtain ⟨P1, Q1, h1⟩ := ih (c + 1) (j + 1)
      obtain ⟨P0, Q0, h0⟩ := ih (c + 1) 0
      set K : ℝ := (q ^ (m + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ with hK
      set A : ℝ := q ^ ((m + 1) * (c + 1)) with hA
      refine ⟨C K * (P1 * Q0 * (C A - X ^ (m + 1)) + X ^ (m + 1) * P0 * Q1),
        Q1 * Q0 * (C A - X ^ (m + 1)), fun w hw hwq => ?_⟩
      obtain ⟨hQ1, hZ1⟩ := h1 w hw hwq
      obtain ⟨hQ0, hZ0⟩ := h0 w hw hwq
      have hApos : (0:ℝ) < A := by rw [hA]; positivity
      have hWA : w ^ (m + 1) < A := by
        rw [hA]
        calc w ^ (m + 1) < q ^ (m + 1) := pow_lt_pow_left₀ hwq hw (by omega)
          _ ≤ q ^ ((m + 1) * (c + 1)) :=
              pow_le_pow_right₀ hq.le (Nat.le_mul_of_pos_right _ (Nat.succ_pos c))
      have hAW : A - w ^ (m + 1) ≠ 0 := by
        have : (0:ℝ) < A - w ^ (m + 1) := by linarith
        exact ne_of_gt this
      constructor
      · simp only [eval_mul, eval_sub, eval_C, eval_pow, eval_X]
        exact mul_ne_zero (mul_ne_zero hQ1 hQ0) hAW
      · rw [twZMass_succ hq hw hwq m c j, hZ1, hZ0, ← hK, ← hA]
        simp only [eval_mul, eval_add, eval_sub, eval_C, eval_pow, eval_X]
        field_simp
