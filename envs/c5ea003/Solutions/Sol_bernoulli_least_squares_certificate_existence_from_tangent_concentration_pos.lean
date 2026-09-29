-- Prove2me | solution 1 for bernoulli_least_squares_certificate_existence_from_tangent_concentration_pos
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T18:30:33.629639+00:00
-- url     : https://prove2.me/submissions/6a52e1a5-b869-49a4-9c09-7ced4d7343ae

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_tangent_sampling_concentration_implies_least_squares_certificate_exists_pos
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped Classical BigOperators

namespace MatrixCompletion

private theorem eventProb_mono_cert {n1 n2 : Nat} (p : Real)
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

/-- Bernoulli least-squares-certificate-existence converter (positive-`p` correction of
the disproved node `bernoulli_least_squares_certificate_existence_from_tangent_concentration`),
proved as a reduction to the pointwise existence core via event monotonicity. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp1 htail
  have hmono := eventProb_mono_cert p (le_of_lt hp) hp1
    (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2))
    (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, LeastSquaresDualCertificate Omega S Y)
    (fun Omega hconc =>
      tangent_sampling_concentration_implies_least_squares_certificate_exists_pos
        Omega S p hp hconc)
  exact le_trans htail hmono
