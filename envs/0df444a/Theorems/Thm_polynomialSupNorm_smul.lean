-- Prove2me | Theorems.Thm_polynomialSupNorm_smul
-- name    : polynomialSupNorm_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:21.525991+00:00
-- url     : https://prove2.me/theorems/05d3e39b-ba97-5635-9e93-cf42e66cf452
-- title:
--   polynomial Sup Norm smul: polynomial Sup Norm smul
-- statement:
--   The polynomial sup norm is homogeneous under complex scalar
--   multiplication.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L50-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L50-L55

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem polynomialSupNorm_smul (a : ℂ) (p : Polynomial ℂ) (X : Set ℂ) :
    polynomialSupNorm (a • p) X = ‖a‖ * polynomialSupNorm p X := by sorry
