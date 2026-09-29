-- Prove2me | solution 1 for quadratic_neumann_correction_bound_from_index_partition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T16:52:51.487123+00:00
-- url     : https://prove2.me/submissions/1663a91f-8e53-489c-9c97-074dfa973928

import Theorems.Thm_second_neumann_certificate_term_spectral_norm_le_index_partition_sum
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open MatrixCompletion

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X + Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) +
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_add_le _ _

private lemma spectralNorm_five_add_le
    {n₁ n₂ : ℕ} (A B C D E : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm ((((A + B) + C) + D) + E) ≤
      (((spectralNorm A + spectralNorm B) + spectralNorm C) +
        spectralNorm D) + spectralNorm E := by
  have hE :
      spectralNorm ((((A + B) + C) + D) + E) ≤
        spectralNorm (((A + B) + C) + D) + spectralNorm E :=
    spectralNorm_add_le (((A + B) + C) + D) E
  have hD :
      spectralNorm (((A + B) + C) + D) ≤
        spectralNorm ((A + B) + C) + spectralNorm D :=
    spectralNorm_add_le ((A + B) + C) D
  have hC :
      spectralNorm ((A + B) + C) ≤
        spectralNorm (A + B) + spectralNorm C :=
    spectralNorm_add_le (A + B) C
  have hB :
      spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B :=
    spectralNorm_add_le A B
  linarith

/--
Source: Candes-Recht 2008, PDF p. 30, equation (6.20), together with the
normal-projection comparison used when passing from the certificate term to the
unprojected quadratic correction.

Equation (6.20) partitions the unprojected quadratic correction
`p⁻¹ (P_Ω - pI) H²(E)` into five index-coincidence classes.  The normal
certificate term is bounded by this unprojected correction in spectral norm; it
is not equal to the five-term sum.  This sketch uses the source-correct
comparison child, then applies the five-term triangle inequality and the five
input bounds.
-/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p C0 C123 C132 C112 Call lam : ℝ) :
    spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
      C0 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
      C123 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
      C132 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
      C112 * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
      Call * Real.rpow lam (-((3 : ℝ) / 2)) →
    NeumannCertificateTermSpectralBound Omega S p 2
      (((((C0 + C123) + C132) + C112) + Call) *
        Real.rpow lam (-((3 : ℝ) / 2))) := by
  intro h0 h123 h132 h112 hall
  unfold NeumannCertificateTermSpectralBound
  let scale := Real.rpow lam (-((3 : ℝ) / 2))
  calc
    spectralNorm (neumannCertificateTerm Omega S p 2)
        ≤ spectralNorm
            ((((quadraticNeumannAllEqualContribution Omega S p +
              quadraticNeumannFirstIndexDistinctContribution Omega S p) +
              quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
              quadraticNeumannLastIndexDistinctContribution Omega S p) +
              quadraticNeumannAllDistinctContribution Omega S p) :=
        second_neumann_certificate_term_spectral_norm_le_index_partition_sum
          S Omega p
    _ ≤
        ((((spectralNorm (quadraticNeumannAllEqualContribution Omega S p) +
          spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p)) +
          spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p)) +
          spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p)) +
          spectralNorm (quadraticNeumannAllDistinctContribution Omega S p)) :=
        spectralNorm_five_add_le _ _ _ _ _
    _ ≤ ((((C0 * scale + C123 * scale) + C132 * scale) + C112 * scale) +
          Call * scale) :=
        add_le_add (add_le_add (add_le_add (add_le_add h0 h123) h132) h112) hall
    _ = (((((C0 + C123) + C132) + C112) + Call) * scale) := by ring
