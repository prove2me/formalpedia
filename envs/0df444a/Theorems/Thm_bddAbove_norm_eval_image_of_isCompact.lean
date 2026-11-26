-- Prove2me | Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
-- name    : bddAbove_norm_eval_image_of_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:59.450045+00:00
-- url     : https://prove2.me/theorems/87371674-41a5-53fa-a332-be5ca721c9c8
-- title:
--   bdd Above norm eval image of is Compact: bdd Above norm eval image of is Compact
-- statement:
--   On a compact set the values `‖p.eval z‖` are bounded above.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L66-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L66-L68

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

theorem bddAbove_norm_eval_image_of_isCompact (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) :
    BddAbove ((fun z => ‖p.eval z‖) '' K) := by sorry
