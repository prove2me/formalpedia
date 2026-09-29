-- Prove2me | solution 1 for bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T18:22:13.437931+00:00
-- url     : https://prove2.me/submissions/6ef259a5-50d6-47e3-9703-d42314cc380c

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped Classical BigOperators

namespace MatrixCompletion

private theorem tangentProjection_zero' {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) :
    tangentProjection S (0 : RealMatrix n1 n2) = 0 := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection
  funext i j
  simp

private theorem frobeniusNormSq_eq_zero_iff' {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNormSq X = 0 ↔ X = 0 := by
  unfold frobeniusNormSq
  constructor
  · intro h
    funext i j
    have hnn : ∀ a ∈ (Finset.univ : Finset (Fin n1)),
        (0 : Real) ≤ ∑ b : Fin n2, X a b ^ 2 :=
      fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)
    have h1 : ∀ a ∈ (Finset.univ : Finset (Fin n1)),
        (∑ b : Fin n2, X a b ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
    have h2 := h1 i (Finset.mem_univ i)
    have hnn2 : ∀ b ∈ (Finset.univ : Finset (Fin n2)), (0 : Real) ≤ X i b ^ 2 :=
      fun b _ => sq_nonneg _
    have h3 : ∀ b ∈ (Finset.univ : Finset (Fin n2)), X i b ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn2).1 h2
    have h4 := h3 j (Finset.mem_univ j)
    have : X i j = 0 := by nlinarith [h4]
    simpa using this
  · intro h; subst h; simp

private theorem frobeniusNorm_smul' {n1 n2 : Nat} (c : Real) (X : RealMatrix n1 n2) :
    frobeniusNorm (c • X) = |c| * frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  have : (∑ i : Fin n1, ∑ j : Fin n2, (c • X) i j ^ 2)
      = c ^ 2 * ∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : (c • X) i j = c * X i j := rfl
    rw [this]; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private theorem pointwise_injective
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real)
    (hp : 0 < p)
    (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) :
    SamplingOperatorInjectiveOnT Omega S := by
  intro H hHT hHsamp
  have hkey := hconc H hHT
  rw [hHsamp, tangentProjection_zero'] at hkey
  have hsub : (0 : RealMatrix n1 n2) - p • H = (-p) • H := by
    rw [zero_sub, neg_smul]
  rw [hsub, frobeniusNorm_smul'] at hkey
  have habs : |(-p)| = p := by rw [abs_neg, abs_of_pos hp]
  rw [habs] at hkey
  have hnormnn : 0 ≤ frobeniusNorm H := Real.sqrt_nonneg _
  have hnorm0 : frobeniusNorm H = 0 := by
    by_contra hne
    have hpos : 0 < frobeniusNorm H := lt_of_le_of_ne hnormnn (Ne.symm hne)
    nlinarith [hkey, hp, hpos]
  have hsq : frobeniusNormSq H = 0 := by
    have hnn : 0 ≤ frobeniusNormSq H := by
      unfold frobeniusNormSq
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have heq : frobeniusNormSq H = frobeniusNorm H ^ 2 := by
      unfold frobeniusNorm; rw [Real.sq_sqrt hnn]
    rw [heq, hnorm0]; ring
  exact (frobeniusNormSq_eq_zero_iff' H).1 hsq

private theorem eventProb_mono {n1 n2 : Nat} (p : Real)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset (Fin n1 × Fin n2) → Prop)
    (hAB : ∀ Omega, A Omega → B Omega) :
    bernoulliEventProb p A ≤ bernoulliEventProb p B := by
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  have hw : 0 ≤ bernoulliObservationWeight p Omega := by
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  by_cases hA : A Omega
  · rw [if_pos hA, if_pos (hAB Omega hA)]
  · rw [if_neg hA]
    by_cases hB : B Omega
    · rw [if_pos hB]; exact hw
    · rw [if_neg hB]

end MatrixCompletion

open MatrixCompletion

/-- Bernoulli injectivity-from-concentration converter (positive-`p` correction
of the disproved node `bernoulli_restricted_sampling_injectivity_from_tangent_concentration`).
Candès–Recht 2009 (arXiv:0805.4471), §4.2, eq. (4.5)/(4.11), p.19–20. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp1 htail
  have hmono := eventProb_mono p (le_of_lt hp) hp1
    (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2))
    (fun Omega => SamplingOperatorInjectiveOnT Omega S)
    (fun Omega hconc => pointwise_injective Omega S p hp hconc)
  exact le_trans htail hmono
