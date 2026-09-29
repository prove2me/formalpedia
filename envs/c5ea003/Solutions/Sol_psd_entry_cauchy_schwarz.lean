-- Prove2me | solution 1 for psd_entry_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:22:52.939948+00:00
-- url     : https://prove2.me/submissions/87bd9a0e-a8b4-481b-a927-474ec2a546f6

-- Sol generated from Bridges/ProbabilityAndStochastics/MatroidHodgeDPP.lean
import Mathlib
import Definitions.Def_Bridges_ProbabilityAndStochastics_MatroidHodgeDPP
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Matroid Hodge Theory and DPP Support Exchange

This file formalizes the connection between determinantal point processes (DPPs),
matroid theory, and Lorentzian polynomial geometry.

## Novel Definitions

* `FinsetMatroid` — Matroid structure via bases on `Finset (Fin n)` with exchange axiom
* `DPPSupport` — Support of a DPP kernel (subsets with positive principal minor)
* `SubmodularFn` — Submodularity condition for set functions
* `DPPSymmetricExchangeProperty` — The testable conjecture

## Main Results

* `finset_matroid_sym_exchange_singleton` — Symmetric exchange for singleton diff
* `psd_all_principal_minors_nonneg` — All principal minors of PSD are nonneg
* `dpp_support_size_one_characterization` — Size-1 DPP support characterization
* `rank1_kernel_psd` — Rank-1 kernels vvᵀ are PSD
* `psd_entry_cauchy_schwarz` — Cauchy-Schwarz for PSD entries
* `uniform_matroid_symmetric_exchange` — Symmetric exchange for uniform matroid
* `total_negdep_eq_frobenius` — Total negative dependence = Frobenius norm

## Cross-Domain: Matroid Theory ↔ Linear Algebra ↔ Probability ↔ Optimization
-/

open Finset BigOperators Matrix

noncomputable section

/-! ## Part I: Matroid Foundations -/




/-! ## Part II: Symmetric Exchange for Singleton Symmetric Difference

When B₁ \ B₂ = {x} and B₂ \ B₁ = {y}, the two bases differ by exactly one
element swap. The reverse swap B₂ - y + x recovers B₁. -/


/-! ## Part III: DPP Support -/




/-! ## Part IV: DPP Support Characterization -/




/-! ## Part V: Submodularity (Cross-Domain: Combinatorics ↔ Optimization) -/



/-! ## Part VI: Rank-1 Kernels -/



/-
A rank-1 kernel vvᵀ is PSD: xᵀ(vvᵀ)x = (vᵀx)² ≥ 0.
    Proof: rewrite xᵀ(vvᵀ)x as (∑ᵢ vᵢxᵢ)² and use sq_nonneg.
-/

/-! ## Part VII: Quantitative Negative Dependence -/




/-! ## Part VIII: PSD Entry Cauchy-Schwarz -/

/-
Cauchy-Schwarz for PSD entries: K_ij² ≤ K_ii · K_jj.
    Proof: 2×2 principal minor det ≥ 0 gives K_ii·K_jj - K_ij² ≥ 0.
-/

/-! ## Part IX: Uniform Matroid and Symmetric Exchange -/


/-
Symmetric exchange for uniform matroid: swapping elements between
    two k-subsets preserves being a k-subset in both directions.
-/

/-! ## Part X: PSD Trace -/


/-! ## Part XI: Complement Identity -/


/-! ## Part XII: Testable Conjecture -/






theorem solution{n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.PosSemidef) (hKsymm : K.IsSymm) (i j : Fin n) :
    K i j ^ 2 ≤ K i i * K j j := by
  -- By the properties of the determinant and the fact that $K$ is positive semidefinite, we have:
  have h_det : Matrix.det (Matrix.of ![![K i i, K i j], ![K j i, K j j]]) ≥ 0 := by
    by_cases hij : i = j;
    · simp [hij];
    · have h_det : Matrix.PosSemidef (Matrix.of ![![K i i, K i j], ![K j i, K j j]]) := by
        have h_submatrix : Matrix.PosSemidef (Matrix.submatrix K (fun k : Fin 2 => if k = 0 then i else j) (fun k : Fin 2 => if k = 0 then i else j)) := by
          exact PosSemidef.submatrix hK fun k => if k = 0 then i else j;
        convert h_submatrix using 1;
        ext k l; fin_cases k <;> fin_cases l <;> rfl;
      convert h_det.det_nonneg;
  simp_all +decide [ Matrix.det_fin_two, pow_two ];
  convert h_det using 1 ; rw [ ← hKsymm.apply ]
