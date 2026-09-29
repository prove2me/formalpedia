-- Prove2me | solution 1 for bernoulli_l2_le_l1_of_l4_le_l2sq
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T06:23:29.397281+00:00
-- url     : https://prove2.me/submissions/9a2bfcc8-f765-4609-873c-cb066a6b4f76

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

/-
de la Peña–Giné Ch. 3 / de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211),
the L4 → L2 → L1 moment-transfer device cited in the proof of the lower bound
(p. 4, eq. after (13)) and in the proof of Lemma 2:

  "for any random variable ξ and positive constant c, ‖ξ‖₄ ≤ c‖ξ‖₂ implies
   ‖ξ‖₂ ≤ c²‖ξ‖₁".

Squaring both sides, on the discrete Bernoulli powerset measure this is exactly:
  E[F⁴] ≤ K·(E[F²])²   ⟹   E[F²] ≤ K·(E[|F|])²,
where K = c⁴.  Proof: two applications of Cauchy–Schwarz on the probability
measure (weights nonneg + sum to 1) — NO fractional powers, NO Mathlib gap.

  (E F²)²  ≤ (E|F|)·(E|F|³)              [CS:  F² = √|F| · √|F|³]
  (E|F|³)² ≤ (E F²)·(E F⁴)              [CS:  |F|³ = √F² · √F⁴]
Combine with E F⁴ ≤ K(E F²)²:
  d² ≤ b·e ≤ K b³ ⇒ d ≤ √K b^{3/2};  b² ≤ a·d ≤ a√K b^{3/2} ⇒ b ≤ K a².

This is the Paley–Zygmund / moment-interpolation building block that the de la
Peña Lemma 2 (hypercontractivity → Paley–Zygmund lower bound) consumes once the
L4↔L2 hypercontractivity hypothesis (e.g. the order-2 symmetric form already
PROVED as `centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity`)
is available.  Stated abstractly over any real statistic `F` for reusability.
-/

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ) (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 → 0 ≤ K →
    bernoulliExpectation p (fun Ω => (F Ω) ^ 4) ≤
        K * (bernoulliExpectation p (fun Ω => (F Ω) ^ 2)) ^ 2 →
    bernoulliExpectation p (fun Ω => (F Ω) ^ 2) ≤
        K * (bernoulliExpectation p (fun Ω => |F Ω|)) ^ 2 := by
  intro hp0 hp1 hK hHC
  classical
  -- weight nonnegativity
  have hw : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Ω := by
    intro Ω
    unfold bernoulliObservationWeight
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg h1p _)
  -- weights sum to one
  have hsum1 : ∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω = 1 := by
    unfold bernoulliObservationWeight
    rw [Fintype.sum_pow_mul_eq_add_pow (Fin n₁ × Fin n₂) p (1 - p)]
    simp
  -- abbreviations for the four moments
  set a : ℝ := bernoulliExpectation p (fun Ω => |F Ω|) with ha
  set b : ℝ := bernoulliExpectation p (fun Ω => (F Ω) ^ 2) with hb
  set d : ℝ := bernoulliExpectation p (fun Ω => |F Ω| ^ 3) with hd
  set e : ℝ := bernoulliExpectation p (fun Ω => (F Ω) ^ 4) with he
  -- nonnegativity of the moments
  have hbnn : 0 ≤ b := by
    rw [hb]; unfold bernoulliExpectation
    exact Finset.sum_nonneg (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
  have hann : 0 ≤ a := by
    rw [ha]; unfold bernoulliExpectation
    exact Finset.sum_nonneg (fun Ω _ => mul_nonneg (hw Ω) (abs_nonneg _))
  have hdnn : 0 ≤ d := by
    rw [hd]; unfold bernoulliExpectation
    exact Finset.sum_nonneg (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
  have henn : 0 ≤ e := by
    rw [he]; unfold bernoulliExpectation
    exact Finset.sum_nonneg (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
  -- CS step 1:  (E F²)² ≤ (E|F|)·(E|F|³)        via  (w·F²)² = (w·|F|)·(w·|F|³)
  have hCS1 : b ^ 2 ≤ a * d := by
    have hineq :
        (∑ Ω : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω * (F Ω) ^ 2) ^ 2 ≤
          (∑ Ω : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Ω * |F Ω|) *
            (∑ Ω : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Ω * |F Ω| ^ 3) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
        (fun Ω _ => mul_nonneg (hw Ω) (abs_nonneg _))
        (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
        (fun Ω _ => ?_)
      -- (w·F²)² = (w·|F|)·(w·|F|³)
      have hF2 : (F Ω) ^ 2 = |F Ω| ^ 2 := (sq_abs (F Ω)).symm
      rw [hF2]
      ring
    rw [hb, ha, hd]
    simpa [bernoulliExpectation] using hineq
  -- CS step 2:  (E|F|³)² ≤ (E F²)·(E F⁴)        via  (w·|F|³)² = (w·F²)·(w·F⁴)
  have hCS2 : d ^ 2 ≤ b * e := by
    have hineq :
        (∑ Ω : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω * |F Ω| ^ 3) ^ 2 ≤
          (∑ Ω : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Ω * (F Ω) ^ 2) *
            (∑ Ω : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Ω * (F Ω) ^ 4) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
        (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
        (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
        (fun Ω _ => ?_)
      -- (w·|F|³)² = (w·F²)·(w·F⁴)
      have hF2 : (F Ω) ^ 2 = |F Ω| ^ 2 := (sq_abs (F Ω)).symm
      have hF4 : (F Ω) ^ 4 = |F Ω| ^ 4 := by
        have : |F Ω| ^ 4 = (|F Ω| ^ 2) ^ 2 := by ring
        rw [this, sq_abs]; ring
      rw [hF2, hF4]
      ring
    rw [hd, hb, he]
    simpa [bernoulliExpectation] using hineq
  -- hypercontractivity hypothesis in the abbreviations:  e ≤ K·b²
  have hHC' : e ≤ K * b ^ 2 := by rw [he, hb]; exact hHC
  -- Algebra:  from d² ≤ b·e ≤ K b³  and  b² ≤ a·d,  conclude  b ≤ K a².
  -- First:  d² ≤ K b³.
  have hd2 : d ^ 2 ≤ K * b ^ 3 := by
    calc d ^ 2 ≤ b * e := hCS2
      _ ≤ b * (K * b ^ 2) := by
            apply mul_le_mul_of_nonneg_left hHC' hbnn
      _ = K * b ^ 3 := by ring
  -- Then:  b⁴ = (b²)² ≤ (a·d)² = a²·d² ≤ a²·K·b³,  giving  b ≤ K a²  (b·b³).
  have hb4 : b ^ 4 ≤ a ^ 2 * (K * b ^ 3) := by
    calc b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ ≤ (a * d) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) hCS1
      _ = a ^ 2 * d ^ 2 := by ring
      _ ≤ a ^ 2 * (K * b ^ 3) := by
            apply mul_le_mul_of_nonneg_left hd2 (by positivity)
  -- Goal is now (in the `set` abbreviations):  b ≤ K * a ^ 2.
  -- b⁴ ≤ K a² b³.  If b = 0, conclusion is trivial; else divide by b³ > 0.
  rcases eq_or_lt_of_le hbnn with hb0 | hbpos
  · -- b = 0 :  goal  0 ≤ K * a ^ 2.
    rw [← hb0]; exact mul_nonneg hK (by positivity)
  · -- b > 0 :  from b⁴ ≤ K a² b³ and b³ > 0, get b ≤ K a².
    have hb3pos : 0 < b ^ 3 := by positivity
    have hrw : b ^ 4 = b * b ^ 3 := by ring
    have hrhs : a ^ 2 * (K * b ^ 3) = (K * a ^ 2) * b ^ 3 := by ring
    rw [hrw, hrhs] at hb4
    exact le_of_mul_le_mul_right hb4 hb3pos
