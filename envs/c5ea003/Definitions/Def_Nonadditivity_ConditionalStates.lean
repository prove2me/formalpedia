-- Prove2me | Definitions.Def_Nonadditivity_ConditionalStates
-- name    : Nonadditivity_ConditionalStates
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:32:50.829952+00:00
-- url     : https://prove2.me/theorems/c1d91014-77ab-4f49-8415-560cc6e90dcd
-- title:
--   Normalization of subnormalized positive quantum states
-- statement:
--   A positive semidefinite finite matrix has real, nonnegative trace. Dividing it by a positive trace produces a density matrix; when the trace vanishes, choose the maximally mixed state as a normalized representative. Multiplying the normalized representative by the original trace recovers the original matrix in both cases, since a positive semidefinite matrix of zero trace is zero. This identity handles zero-probability branches in controlled channel decompositions.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ConditionalStates.lean#L22-L51

import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # Normalizing subnormalized positive states

Zero-probability branches are handled explicitly. This is the matrix
decomposition needed when a classical input register is measured.
-/

noncomputable section

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem positive_trace_real (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (A.trace.re : ℂ) = A.trace := by
  exact (Complex.eq_re_of_ofReal_le hA.trace_nonneg).symm

omit [DecidableEq ι] [Nonempty ι] in
theorem positive_trace_re_nonneg (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1

/-- Conditional state of a positive matrix, with an arbitrary fixed state on
the zero-probability branch. -/
def normalizePositive (A : Matrix ι ι ℂ) (hA : A.PosSemidef) : DensityMatrix ι :=
  if h : A.trace.re = 0 then maximallyMixed ι else
    { matrix := (((A.trace.re)⁻¹ : ℝ) : ℂ) • A
      positive := hA.smul (by exact_mod_cast inv_nonneg.mpr (positive_trace_re_nonneg A hA))
      normalized := by
        rw [Matrix.trace_smul, smul_eq_mul, ← positive_trace_real A hA]
        simp only [Complex.ofReal_re, ← Complex.ofReal_mul, inv_mul_cancel₀ h,
          Complex.ofReal_one] }

/-- Renormalization exactly recovers the original positive matrix, including
the zero-trace case. -/
theorem trace_smul_normalizePositive (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (A.trace.re : ℂ) • (normalizePositive A hA).matrix = A := by
  by_cases h : A.trace.re = 0
  · have hz : A.trace = 0 := by rw [← positive_trace_real A hA, h]; simp
    have hzero := hA.trace_eq_zero_iff.mp hz
    simp [hzero]
  · simp only [normalizePositive, dif_neg h, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ h, Complex.ofReal_one, one_smul]

end Nonadditivity.Entropy


