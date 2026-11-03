-- Prove2me | Theorems.Thm_levy_foundations_covarianceMatrixPosSemidef
-- name    : levy_foundations_covarianceMatrixPosSemidef
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:25:47.716983+00:00
-- url     : https://prove2.me/theorems/d67e209c-8058-412e-9204-9c098c7290c0
-- title:
--   Positive definiteness makes the finite covariance kernel matrix positive semidefinite
-- statement:
--   Positive definiteness makes the finite covariance kernel matrix positive semidefinite.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Representation/BochnerGaussian.lean#L48

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_covarianceMatrix
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Matrix Complex
open scoped ComplexOrder

theorem levy_foundations_covarianceMatrixPosSemidef {n : ℕ}
    (ψ : ℝ → ℂ) (t : Fin n → ℝ)
    (hψ : LevyFoundations.isPositiveDefinite ψ) :
    (LevyFoundations.covarianceMatrix ψ t).PosSemidef := by sorry
