-- Prove2me | solution 1 for Zeta23.MV.abs_eigenvalue_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:26:16.204093+00:00
-- url     : https://prove2.me/submissions/eb0a19b5-cf72-419f-a9c6-1f4d6e4b4676

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_MV
import Definitions.Def_Zeta23_MV_Duality
import Definitions.Def_Zeta23_MV_Spacing

-- from Zeta23.MV.Duality
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Zeta23/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV


variable {ι : Type} [Fintype ι] [DecidableEq ι]












end MV
end Zeta23

end
open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (j : ι) :
    |(Mmat_isHermitian freq δ).eigenvalues j| ≤ C := by
  set hM := Mmat_isHermitian freq δ
  set ν : ℝ := hM.eigenvalues j
  set v : ι → ℂ := ⇑(hM.eigenvectorBasis j) with hvdef
  have hv : Mmat freq δ *ᵥ v = ν • v := hM.mulVec_eigenvectorBasis j
  have hunit : ∑ n, ‖v n‖ ^ 2 = 1 := by
    have h1 : ‖hM.eigenvectorBasis j‖ = 1 := hM.eigenvectorBasis.orthonormal.1 j
    rw [← EuclideanSpace.norm_sq_eq, h1, one_pow]
  -- the eigen-relation in `eigen_bound`'s shape, with μ := −ν
  have heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n
        = ((-ν : ℝ) : ℂ) * Complex.I * v m := by
    intro m
    have hm := congrFun hv m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at hm
    -- Σ_s (k m s) I v s = ν v m ; drop the diagonal term (k m m = 0)
    have hsplit : ∑ s, Mmat freq δ m s * v s
        = ∑ s ∈ Finset.univ.erase m, (kfun freq δ m s : ℂ) * Complex.I * v s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
      simp [Mmat, kfun]
    rw [hsplit] at hm
    have hk : ∀ s ∈ Finset.univ.erase m, (kfun freq δ m s : ℂ) * Complex.I * v s
        = Complex.I * (((Real.sqrt (δ m) * Real.sqrt (δ s) / (freq m - freq s) : ℝ) : ℂ) * v s) := by
      intro s hs
      have hsm : m ≠ s := fun e => (Finset.mem_erase.mp hs).1 e.symm
      simp only [kfun, if_neg hsm]; ring
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum] at hm
    -- I * X = ν v_m  ⇒  X = (−ν) I v_m
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    calc ∑ n ∈ Finset.univ.erase m,
          ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n
        = -Complex.I * (Complex.I * ∑ n ∈ Finset.univ.erase m,
            ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = -Complex.I * ((ν : ℂ) * v m) := by rw [hm]
      _ = ((-ν : ℝ) : ℂ) * Complex.I * v m := by push_cast; ring
  have := hb ι freq δ h v hunit (-ν) heig
  simpa using this
