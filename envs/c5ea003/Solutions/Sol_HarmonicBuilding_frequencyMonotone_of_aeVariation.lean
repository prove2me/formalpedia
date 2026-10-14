-- Prove2me | solution 1 for HarmonicBuilding.frequencyMonotone_of_aeVariation
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T10:54:48.181945+00:00
-- url     : https://prove2.me/submissions/01094c2e-de99-420f-beca-68281c7b3a4f

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open Set MeasureTheory Filter
open scoped Topology intervalIntegral

/-! Almost-everywhere frequency calculus from Gromov--Schoen (1992),
Section 2, equations (2.2)--(2.5), pp. 192--194. The flux J is retained
separately from the energy; only E <= J is used. -/

namespace FrequencyVariationAnalysis

lemma ac_of_dist_bound {f g : ℝ → ℝ} {a b K : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b,
      dist (g x) (g y) ≤ K * dist (f x) (f y)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun s hs hlen => ?_⟩
  have hd' := hd s hs hlen
  calc
    ∑ i ∈ Finset.range s.1, dist (g (s.2 i).1) (g (s.2 i).2) ≤
        ∑ i ∈ Finset.range s.1, K * dist (f (s.2 i).1) (f (s.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound _ (hs.1 i hi).1 _ (hs.1 i hi).2
    _ = K * ∑ i ∈ Finset.range s.1, dist (f (s.2 i).1) (f (s.2 i).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hd'.le hK
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field_simp

lemma ac_reciprocal {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < f x) :
    AbsolutelyContinuousOnInterval (fun x => 1 / f x) a b := by
  obtain ⟨t, ht, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  have htP := hpos t ht
  apply ac_of_dist_bound hf (K := 1 / (f t * f t)) (by positivity)
  intro x hx y hy
  have hxP := hpos x hx
  have hyP := hpos y hy
  have he : 1 / f x - 1 / f y = (f y - f x) / (f x * f y) := by
    field_simp
  rw [Real.dist_eq, he, abs_div, abs_mul, abs_of_pos hxP, abs_of_pos hyP]
  calc
    |f y - f x| / (f x * f y) ≤ |f y - f x| / (f t * f t) := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      exact mul_le_mul (hmin hx) (hmin hy) htP.le hxP.le
    _ = (1 / (f t * f t)) * dist (f x) (f y) := by
      rw [Real.dist_eq, abs_sub_comm]
      ring

lemma frequencyMonotone_of_aeVariation (R : ℝ) (E I J F : ℝ → ℝ)
    (hI : ∀ r ∈ Ioo (0 : ℝ) R, 0 < I r)
    (hE : ∀ r ∈ Ioo (0 : ℝ) R, 0 ≤ E r)
    (hAC : ∀ a b : ℝ, 0 < a → a ≤ b → b < R →
      AbsolutelyContinuousOnInterval E a b ∧ AbsolutelyContinuousOnInterval I a b)
    (hvar : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt I (I r / r + 2 * J r) r ∧
      HasDerivAt E (2 * F r) r ∧ E r ≤ J r ∧ J r ^ 2 ≤ I r * F r) :
    MonotoneOn (fun r => r * E r / I r) (Ioo (0 : ℝ) R) := by
  intro a ha b hb hab
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) R := by
    rw [uIcc_of_le hab]
    intro x hx
    exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  obtain ⟨hAE, hAI⟩ := hAC a b ha.1 hab hb.2
  have hAR : AbsolutelyContinuousOnInterval (fun r : ℝ => r) a b :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hAinv := ac_reciprocal hAI (fun x hx => hI x (hsub hx))
  have hAQ : AbsolutelyContinuousOnInterval (fun r => r * E r / I r) a b := by
    convert! (hAR.mul hAE).mul hAinv using 1
    ext r
    simp [div_eq_mul_inv]
  have hnonneg : ∀ᵐ r : ℝ, r ∈ uIcc a b → 0 ≤ deriv (fun s => s * E s / I s) r := by
    filter_upwards [hvar] with r hr hrab
    have hrR := hsub hrab
    have hrP := hrR.1
    have hIP := hI r hrR
    have hEP := hE r hrR
    obtain ⟨hId, hEd, hEJ, hCS⟩ := hr hrR
    have hJP : 0 ≤ J r := hEP.trans hEJ
    have hnum : 0 ≤ I r * F r - E r * J r := by
      nlinarith [mul_le_mul_of_nonneg_right hEJ hJP]
    have hder : HasDerivAt (fun s => s * E s / I s)
        (2 * r * (I r * F r - E r * J r) / I r ^ 2) r := by
      convert! (((hasDerivAt_id r).mul hEd).div hId (ne_of_gt hIP)) using 1
      simp only [Pi.mul_apply, id_eq]
      field_simp [ne_of_gt hrP, ne_of_gt hIP]
      ring
    rw [hder.deriv]
    exact div_nonneg (mul_nonneg (by positivity) hnum) (sq_nonneg _)
  have hint : 0 ≤ ∫ r in a..b, deriv (fun s => s * E s / I s) r := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    filter_upwards [ae_restrict_of_ae hnonneg, ae_restrict_mem measurableSet_Icc] with r hr hrab
    exact hr (by rwa [uIcc_of_le hab])
  rw [hAQ.integral_deriv_eq_sub] at hint
  exact sub_nonneg.mp hint

end FrequencyVariationAnalysis

open FrequencyVariationAnalysis

theorem solution (R : ℝ) (E I J F : ℝ → ℝ)
    (hI : ∀ r ∈ Ioo (0 : ℝ) R, 0 < I r)
    (hE : ∀ r ∈ Ioo (0 : ℝ) R, 0 ≤ E r)
    (hAC : ∀ a b : ℝ, 0 < a → a ≤ b → b < R →
      AbsolutelyContinuousOnInterval E a b ∧ AbsolutelyContinuousOnInterval I a b)
    (hvar : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt I (I r / r + 2 * J r) r ∧
      HasDerivAt E (2 * F r) r ∧ E r ≤ J r ∧ J r ^ 2 ≤ I r * F r) :
    MonotoneOn (fun r => r * E r / I r) (Ioo (0 : ℝ) R) :=
  frequencyMonotone_of_aeVariation R E I J F hI hE hAC hvar

#print axioms solution
