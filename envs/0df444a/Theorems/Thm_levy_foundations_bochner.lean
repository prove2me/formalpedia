-- Prove2me | Theorems.Thm_levy_foundations_bochner
-- name    : levy_foundations_bochner
-- status  : Open
-- author  : @WillR
-- created : 2026-10-27T07:47:39.748675+00:00
-- url     : https://prove2.me/theorems/7b51dc81-b9d5-4524-b586-392469091ebc
-- title:
--   Bochner representation in the characteristic-function convention
-- statement:
--   A continuous positive-definite function on ℝ normalised at zero is the characteristic function of a probability measure, with Fourier convention exp(i ξ x). A published Bochner theorem with convention exp(i 2π ξ x) is referenced; the conversion must be proved explicitly.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/Bochner.lean#L1573-L1577. Source Bochner theorem; existing Prove2Me theorem Bochner.bochner_theorem uses 2π scaling. Independent Prove2Me statement, pending audit and remote compilation.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory

theorem levy_foundations_bochner
    (φ : ℝ → ℂ) (hφc : Continuous φ)
    (hpd : LevyFoundations.isPositiveDefinite φ) (h0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ : ℝ, charFun (μ : Measure ℝ) ξ = φ ξ := by sorry
