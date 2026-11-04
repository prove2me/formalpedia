-- Prove2me | Theorems.Thm_levy_foundations_posDefPointwiseMul
-- name    : levy_foundations_posDefPointwiseMul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:08:03.295021+00:00
-- url     : https://prove2.me/theorems/4e3ea3db-2950-4336-9e83-92725518c857
-- title:
--   Schur product closure for positive-definite functions
-- statement:
--   Schur product closure for positive-definite functions.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L132

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

theorem levy_foundations_posDefPointwiseMul
    {φ ψ : ℝ → ℂ} (hφ : LevyFoundations.isPositiveDefinite φ)
    (hψ : LevyFoundations.isPositiveDefinite ψ) :
    LevyFoundations.isPositiveDefinite (fun x => φ x * ψ x) := by sorry
