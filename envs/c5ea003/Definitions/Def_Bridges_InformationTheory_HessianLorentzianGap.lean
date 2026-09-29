-- Prove2me | Definitions.Def_Bridges_InformationTheory_HessianLorentzianGap
-- name    : Bridges_InformationTheory_HessianLorentzianGap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:55.759166+00:00
-- url     : https://prove2.me/theorems/82e6c569-cb72-4a37-bbbb-eedd562dcede
-- title:
--   Aether Catalog definitions — Bridges_InformationTheory_HessianLorentzianGap
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InformationTheory.HessianLorentzianGap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InformationTheory/HessianLorentzianGap.lean by skeleton subtraction
import Mathlib
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

namespace HessianLorentzianGap

/-! ## §1. Core Definitions -/


/-- The Hadamard (entrywise) square of a matrix: (K⊙K)_{ij} = K_{ij}². -/
def hadamardSq {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K i j * K i j

/-- The outer product of the diagonal: (d·dᵀ)_{ij} = K_{ii}·K_{jj}. -/
def diagOuterProduct {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K i i * K j j

/-- The principal minor matrix: H_{ij} = K_{ii}·K_{jj} - K_{ij}².
    This equals the matrix of 2×2 principal minors of K. -/
def principalMinorMatrix {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K i i * K j j - K i j * K i j

/-! ## §2. Structural Properties -/






/-
For a PSD matrix K, each 2×2 principal minor is nonneg:
    K_{ii}·K_{jj} ≥ K_{ij}². This is Cauchy-Schwarz for the PSD inner product.
-/



/-! ## §3. Sum Identities -/



/-! ## §4. Perturbation Theory -/


/-! ## §5. Lorentzian Structure Definitions -/



/-- The Lorentzian gap parameter: the total sum of the principal minor matrix.
    Equals (tr K)² - ‖K‖_F². A positive gap is necessary for Lorentzian signature. -/
def lorentzianGapParam {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, H i j


/-! ## §6. Concrete 2×2 Case -/



/-! ## §7. Projection Analysis (K² = K) -/





/-! ## §8. Cross-Domain: DPP Diversity ↔ Spectral Structure -/


/-! ## §9. Information-Theoretic Connection -/

/-- The von Neumann entropy functional of a DPP kernel.
    S(K) = -∑ᵢ [K_{ii} log K_{ii} + (1-K_{ii}) log(1-K_{ii})].
    Provides an upper bound on the Shannon entropy of the DPP distribution. -/
def dppEntropy {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -∑ i : Fin n, (K i i * Real.log (K i i) + (1 - K i i) * Real.log (1 - K i i))

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


end HessianLorentzianGap

end


