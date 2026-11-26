-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary
-- name    : norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:52.485347+00:00
-- url     : https://prove2.me/theorems/a3057350-3d2f-570d-8b63-71c7d5e27aaa
-- title:
--   norm aeval le polynomial Sup Norm closed Ball of mem unitary: norm aeval le polynomial Sup Norm closed Ball of mem unitary
-- statement:
--   **Von Neumann's inequality for unitaries**, in any C*-algebra: for `U` unitary,
--   `‖p(U)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖`. Since `p(U)` is normal, `‖p(U)‖` is its spectral radius, and
--   `σ(p(U)) = p(σ(U))` with `σ(U)` contained in the unit circle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L75-L99
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L75-L99

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u

theorem norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary {A : Type*} [CStarAlgebra A]
    {U : A} (hU : U ∈ unitary A) (p : ℂ[X]) :
    ‖aeval U p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by sorry
