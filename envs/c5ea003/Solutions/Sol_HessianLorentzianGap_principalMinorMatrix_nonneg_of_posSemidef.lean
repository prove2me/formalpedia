-- Prove2me | solution 1 for HessianLorentzianGap.principalMinorMatrix_nonneg_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:14.049125+00:00
-- url     : https://prove2.me/submissions/3c9ff96b-af87-46eb-a640-5dca3aff1f6b

-- Sol generated from Bridges/InformationTheory/HessianLorentzianGap.lean
import Mathlib
import Definitions.Def_Bridges_InformationTheory_HessianLorentzianGap
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Hessian-Based Lorentzian Gap from DPP Infrastructure

This file develops the theory connecting Hessian matrices of determinantal point process
(DPP) generating polynomials to Lorentzian spectral structure. The key insight is that
the Hessian of a DPP generating polynomial at the all-ones vector equals the matrix of
2×2 principal minors of the correlation kernel K:

  H_{ij} = K_{ii}·K_{jj} - K_{ij}²

In matrix form: H = d·dᵀ - K ⊙ K, where d = diag(K) and ⊙ is the Hadamard product.

## Main Definitions

* `DPP` — Determinantal point process with bounded symmetric PSD kernel
* `principalMinorMatrix` — The matrix of 2×2 principal minors of K
* `hadamardSq` — The Hadamard (entrywise) square of a matrix
* `diagOuterProduct` — The rank-1 matrix d·dᵀ from diagonal entries
* `dppEntropy` — Von Neumann entropy functional of a DPP kernel
* `HasLorentzianSignature` — Quadratic form with at most one positive direction

## Main Results

* `principalMinorMatrix_eq_rank1_minus_hadamard` — H = d·dᵀ - K⊙K decomposition
* `principalMinorMatrix_isHermitian` — Symmetry of the principal minor matrix
* `principalMinorMatrix_diag_zero` — Diagonal entries of H vanish
* `principalMinorMatrix_nonneg_of_posSemidef` — H_{ij} ≥ 0 for PSD K
* `principalMinorMatrix_entry_sum` — Sum identity: (tr K)² - ‖K‖_F²
* `principalMinorMatrix_perturbation` — Exact perturbation formula for H
* `projection_gap_param` — Gap parameter k²-k for projections
* `dpp_expected_diversity` — DPP diversity = (tr K)² - ‖K‖_F²
* `principalMinorMatrix_smul` — Quadratic scaling under scalar multiplication
* `frobenius_lower_bound` — Cauchy-Schwarz for diagonal sums

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Kulesza–Taskar, "Determinantal Point Processes for Machine Learning", 2012
-/

open Finset BigOperators Matrix

noncomputable section

open HessianLorentzianGap

/-! ## §1. Core Definitions -/





/-! ## §2. Structural Properties -/






/-
For a PSD matrix K, each 2×2 principal minor is nonneg:
    K_{ii}·K_{jj} ≥ K_{ij}². This is Cauchy-Schwarz for the PSD inner product.
-/



/-! ## §3. Sum Identities -/



/-! ## §4. Perturbation Theory -/


/-! ## §5. Lorentzian Structure Definitions -/





/-! ## §6. Concrete 2×2 Case -/



/-! ## §7. Projection Analysis (K² = K) -/





/-! ## §8. Cross-Domain: DPP Diversity ↔ Spectral Structure -/


/-! ## §9. Information-Theoretic Connection -/


/-
The DPP entropy is nonneg when diagonal entries are in (0,1),
    since x log x + (1-x) log(1-x) ≤ 0 for x ∈ (0,1).
-/

/-! ## §10. Quantitative Bounds -/

/-
Cauchy-Schwarz for sums: (∑ᵢ aᵢ)² ≤ n · ∑ᵢ aᵢ².
    Applied to diagonal entries, this bounds the gap parameter from above.
-/

/-! ## §11. Scaling and Monotonicity -/







/-! ## §12. Conjecture -/


/-! ## §13. Projection Diversity Bound -/




open HessianLorentzianGap in
theorem solution{n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef) (i j : Fin n) :
    0 ≤ principalMinorMatrix K i j := by
  simp only [principalMinorMatrix]
  -- By the properties of the determinant and the fact that $K$ is positive semidefinite, we have $\det(K_{\{i,j\}}) \geq 0$.
  have h_det_nonneg : Matrix.PosSemidef (Matrix.of ![![K i i, K i j], ![K j i, K j j]]) := by
    have h_submatrix : Matrix.PosSemidef (Matrix.of ![![K i i, K i j], ![K j i, K j j]]) := by
      have h_submatrix : ∃ (P : Matrix (Fin 2) (Fin n) ℝ), Matrix.of ![![K i i, K i j], ![K j i, K j j]] = P * K * P.transpose := by
        use Matrix.of (fun k l => if k = 0 then if l = i then 1 else 0 else if l = j then 1 else 0);
        ext k l; fin_cases k <;> fin_cases l <;> simp +decide [ Matrix.mul_apply ] ;
      obtain ⟨ P, hP ⟩ := h_submatrix;
      convert hK.conjTranspose_mul_mul_same P.transpose using 1;
    exact h_submatrix;
  convert h_det_nonneg.det_nonneg using 1 ; norm_num [ Matrix.det_fin_two ];
  exact Or.inl ( hK.1.apply _ _ )
