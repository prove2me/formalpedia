-- Prove2me | Theorems.Thm_HessianLorentzianGap_principalMinorMatrix_nonneg_of_posSemidef
-- name    : HessianLorentzianGap.principalMinorMatrix_nonneg_of_posSemidef
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:22.890479+00:00
-- url     : https://prove2.me/theorems/0c90f2b5-667d-483a-a67d-77d33c81e8e7
-- title:
--   PrincipalMinorMatrix nonneg of posSemidef
-- statement:
--   Formal statement of `HessianLorentzianGap.principalMinorMatrix_nonneg_of_posSemidef` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HessianLorentzianGap.principalMinorMatrix_nonneg_of_posSemidef{n : ℕ}
--       (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef) (i j : Fin n) :
--       0 ≤ principalMinorMatrix K i j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InformationTheory/HessianLorentzianGap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InformationTheory/HessianLorentzianGap.lean#L121

-- Thm stub generated from Bridges/InformationTheory/HessianLorentzianGap.lean
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

theorem HessianLorentzianGap.principalMinorMatrix_nonneg_of_posSemidef{n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef) (i j : Fin n) :
    0 ≤ principalMinorMatrix K i j := by sorry
