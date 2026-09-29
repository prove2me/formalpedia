-- Prove2me | solution 1 for neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T23:29:24.992581+00:00
-- url     : https://prove2.me/submissions/b5dc21c8-7d21-424a-8af4-8cb7932e00e6

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_least_squares_certificate_neumann_partial_tendsto_pos
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
Reduction of `neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos`
(22bf6cfe_pos) to the §4.3 Neumann convergence core
`least_squares_certificate_neumann_partial_tendsto_pos`.

The corrected node adds `0 < p` and `TangentSamplingConcentration Omega S p (1/2)`
(the §4.2 invertibility input).  Granting the convergence core (partial Neumann sums
converge to `P_{T^perp} Y`), the spectral norm is bounded by `3·(1/8)+1/2 = 7/8 < 1`
via spectral-norm subadditivity, continuity and `le_of_tendsto`.

Source: Candès–Recht 2009 (arXiv:0805.4471), §4.2–4.3: with `0 < p` and the
concentration bound `p^{-1}‖P_T P_Ω P_T − pP_T‖ ≤ 1/2`, the operator `P_T P_Ω P_T`
is invertible on `T`, the least-squares certificate's normal part is the convergent
Neumann series `Σ_k neumannCertificateTerm`, and the term/tail estimates bound it
below `1`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Matrix Filter Topology

variable {n₁ n₂ : ℕ}

/-! ## spectralNorm: subadditive + continuous seminorm. -/

theorem spectralNorm_nonneg (X : RealMatrix n₁ n₂) : 0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

theorem spectralNorm_zero : spectralNorm (0 : RealMatrix n₁ n₂) = 0 := by
  unfold spectralNorm; simp

theorem spectralNorm_add_le (A B : RealMatrix n₁ n₂) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [show toEuclideanLin (A + B) = toEuclideanLin A + toEuclideanLin B from map_add _ _ _]
  rw [show LinearMap.toContinuousLinearMap (toEuclideanLin A + toEuclideanLin B)
        = LinearMap.toContinuousLinearMap (toEuclideanLin A)
          + LinearMap.toContinuousLinearMap (toEuclideanLin B) from map_add _ _ _]
  exact norm_add_le _ _

theorem spectralNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → RealMatrix n₁ n₂) :
    spectralNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, spectralNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [spectralNorm_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (spectralNorm_add_le _ _) (by linarith [ih])

/-- The matrix → continuous-linear-map assignment, as a linear map (so it is
continuous by finite-dimensionality, with the codomain a genuine normed space). -/
noncomputable def toCLMmat :
    RealMatrix n₁ n₂ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n₂) →L[ℝ] EuclideanSpace ℝ (Fin n₁)) where
  toFun := fun X => LinearMap.toContinuousLinearMap (toEuclideanLin X)
  map_add' := by intro A B; simp [map_add]
  map_smul' := by intro c A; simp [map_smul]

theorem continuous_spectralNorm :
    Continuous (fun X : RealMatrix n₁ n₂ => spectralNorm X) := by
  have hc : Continuous (toCLMmat (n₁ := n₁) (n₂ := n₂)) :=
    (toCLMmat (n₁ := n₁) (n₂ := n₂)).continuous_of_finiteDimensional
  exact continuous_norm.comp hc

/-! ## Assembly. -/

variable {r : ℕ} {M : RealMatrix n₁ n₂}

theorem partialSum_spectral_le
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ)
    (hb0 : NeumannCertificateTermSpectralBound Omega S p 0 ((1:ℝ)/8))
    (hb1 : NeumannCertificateTermSpectralBound Omega S p 1 ((1:ℝ)/8))
    (hb2 : NeumannCertificateTermSpectralBound Omega S p 2 ((1:ℝ)/8))
    (hbt : NeumannCertificateTailSpectralBound Omega S p 3 ((1:ℝ)/2))
    (K : ℕ) (hK : 3 ≤ K) :
    spectralNorm (∑ k ∈ Finset.range (K + 1),
        neumannCertificateTerm Omega S p k) ≤ (7:ℝ)/8 := by
  have hsplit : Finset.range (K + 1) = Finset.range 3 ∪ Finset.Icc 3 K := by
    ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.range 3) (Finset.Icc 3 K) := by
    rw [Finset.disjoint_left]; intro x hx hx2
    simp only [Finset.mem_range] at hx; simp only [Finset.mem_Icc] at hx2; omega
  rw [hsplit, Finset.sum_union hdisj]
  refine le_trans (spectralNorm_add_le _ _) ?_
  have hhead : spectralNorm (∑ k ∈ Finset.range 3,
      neumannCertificateTerm Omega S p k) ≤ (3:ℝ)/8 := by
    refine le_trans (spectralNorm_sum_le _ _) ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    unfold NeumannCertificateTermSpectralBound at hb0 hb1 hb2
    linarith [hb0, hb1, hb2]
  have htail : spectralNorm (∑ k ∈ Finset.Icc 3 K,
      neumannCertificateTerm Omega S p k) ≤ (1:ℝ)/2 := by
    unfold NeumannCertificateTailSpectralBound at hbt
    exact hbt K hK
  linarith [hhead, htail]

theorem normal_bound_from_core
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) (Y : RealMatrix n₁ n₂)
    (hb0 : NeumannCertificateTermSpectralBound Omega S p 0 ((1:ℝ)/8))
    (hb1 : NeumannCertificateTermSpectralBound Omega S p 1 ((1:ℝ)/8))
    (hb2 : NeumannCertificateTermSpectralBound Omega S p 2 ((1:ℝ)/8))
    (hbt : NeumannCertificateTailSpectralBound Omega S p 3 ((1:ℝ)/2))
    (hTend : Filter.Tendsto
        (fun K => ∑ k ∈ Finset.range (K + 1), neumannCertificateTerm Omega S p k)
        Filter.atTop (nhds (normalProjection S Y))) :
    spectralNorm (normalProjection S Y) < 1 := by
  have hcont : Filter.Tendsto
      (fun K => spectralNorm (∑ k ∈ Finset.range (K + 1),
        neumannCertificateTerm Omega S p k))
      Filter.atTop (nhds (spectralNorm (normalProjection S Y))) :=
    (continuous_spectralNorm.tendsto _).comp hTend
  have hle : spectralNorm (normalProjection S Y) ≤ (7:ℝ)/8 := by
    refine le_of_tendsto hcont ?_
    filter_upwards [Filter.eventually_ge_atTop 3] with K hK
    exact partialSum_spectral_le Omega S p hb0 hb1 hb2 hbt K hK
  linarith [hle]

end MatrixCompletion

open MatrixCompletion
open scoped Classical BigOperators
open Filter Topology

/-- Reduction: `22bf6cfe_pos` follows from the convergence core
`least_squares_certificate_neumann_partial_tendsto_pos`. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    NeumannCertificateTermSpectralBound Omega S p 0 ((1 : ℝ) / 8) →
    NeumannCertificateTermSpectralBound Omega S p 1 ((1 : ℝ) / 8) →
    NeumannCertificateTermSpectralBound Omega S p 2 ((1 : ℝ) / 8) →
    NeumannCertificateTailSpectralBound Omega S p 3 ((1 : ℝ) / 2) →
    ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      LeastSquaresDualCertificate Omega S Y →
      spectralNorm (normalProjection S Y) < 1 := by
  intro hp hconc hb0 hb1 hb2 hbt Y hY
  have hTend := least_squares_certificate_neumann_partial_tendsto_pos
    Omega S p hp hconc Y hY
  exact normal_bound_from_core Omega S p Y hb0 hb1 hb2 hbt hTend
