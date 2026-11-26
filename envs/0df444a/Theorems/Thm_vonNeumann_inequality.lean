-- Prove2me | Theorems.Thm_vonNeumann_inequality
-- name    : vonNeumann_inequality
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:48.105309+00:00
-- url     : https://prove2.me/theorems/31b8a5b1-62d9-4355-80cf-0e4ed460ccac
-- title:
--   von Neumann inequality: von Neumann inequality
-- statement:
--   **Von Neumann's inequality**: for a contraction `T` and a polynomial `p`,
--   `‖p(T)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L150-L153
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L150-L153

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_inequality (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by sorry
