-- Prove2me | Theorems.Thm_levy_foundations_posDefPointwiseLimit
-- name    : levy_foundations_posDefPointwiseLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:08:16.861272+00:00
-- url     : https://prove2.me/theorems/afd2a8ed-96c9-43ee-b6a3-ad8997744828
-- title:
--   Pointwise sequential limits preserve positive definiteness
-- statement:
--   Pointwise sequential limits preserve positive definiteness.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L212

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

theorem levy_foundations_posDefPointwiseLimit
    {φs : ℕ → ℝ → ℂ}
    (hφs : ∀ n, LevyFoundations.isPositiveDefinite (φs n))
    {φ : ℝ → ℂ} (hlim : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    LevyFoundations.isPositiveDefinite φ := by sorry
