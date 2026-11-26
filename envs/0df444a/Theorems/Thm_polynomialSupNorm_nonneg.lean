-- Prove2me | Theorems.Thm_polynomialSupNorm_nonneg
-- name    : polynomialSupNorm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:32.461522+00:00
-- url     : https://prove2.me/theorems/a412fb2a-9d71-4175-b8fe-e761fad94bca
-- title:
--   polynomial Sup Norm nonneg: polynomial Sup Norm nonneg
-- statement:
--   The polynomial sup-norm is nonnegative.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L47-L48
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L47-L48

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

theorem polynomialSupNorm_nonneg (p : ℂ[X]) (X : Set ℂ) : 0 ≤ polynomialSupNorm p X := by sorry
