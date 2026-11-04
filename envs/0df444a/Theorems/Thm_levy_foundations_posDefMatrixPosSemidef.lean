-- Prove2me | Theorems.Thm_levy_foundations_posDefMatrixPosSemidef
-- name    : levy_foundations_posDefMatrixPosSemidef
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:07:52.789774+00:00
-- url     : https://prove2.me/theorems/1b70aa7d-9c51-41aa-8883-39811fd6644c
-- title:
--   Finite kernel matrix of a positive-definite function is positive semidefinite
-- statement:
--   Finite kernel matrix of a positive-definite function is positive semidefinite.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L109

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

theorem levy_foundations_posDefMatrixPosSemidef
    {φ : ℝ → ℂ} (hφ : LevyFoundations.isPositiveDefinite φ)
    (m : ℕ) (x : Fin m → ℝ) :
    (Matrix.of fun i j : Fin m => φ (x i - x j)).PosSemidef := by sorry
