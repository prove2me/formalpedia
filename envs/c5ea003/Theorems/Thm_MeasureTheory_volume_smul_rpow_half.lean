-- Prove2me | Theorems.Thm_MeasureTheory_volume_smul_rpow_half
-- name    : MeasureTheory.volume_smul_rpow_half
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T13:28:15.673969+00:00
-- url     : https://prove2.me/theorems/9a38b820-63f0-48fd-a662-e4d1d96ea320
-- title:
--   Square root of planar volume under dilation
-- statement:
--   Dilating a planar set by $a\ge0$ scales the square root of its volume linearly in $a$. Follows from addHaar scaling plus ENNReal rpow algebra.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/Volume.lean#L9-L16

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
open scoped Pointwise
open MeasureTheory

namespace MeasureTheory

theorem volume_smul_rpow_half (S : Set (EuclideanSpace ℝ (Fin 2))) (a : ℝ) (ha : 0 ≤ a) : volume (a • S) ^ (2 : ℝ)⁻¹ = ENNReal.ofReal a * volume S ^ (2 : ℝ)⁻¹ := by sorry

end MeasureTheory
