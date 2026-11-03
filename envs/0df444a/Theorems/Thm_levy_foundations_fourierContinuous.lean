-- Prove2me | Theorems.Thm_levy_foundations_fourierContinuous
-- name    : levy_foundations_fourierContinuous
-- status  : Open
-- author  : @WillR
-- created : 2026-10-27T00:14:32.842251+00:00
-- url     : https://prove2.me/theorems/e6f50331-74e8-411a-be22-e345dd81ac44
-- title:
--   Continuity of finite-measure Fourier transforms
-- statement:
--   The Fourier transform of any finite Borel measure on ℝ is continuous in its frequency.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/MeasureFourier.lean#L54-L66. Dominated-convergence theorem. Independent Prove2Me statement, pending audit and remote compilation.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Definitions.Def_levy_foundations_measureFourier

open MeasureTheory

theorem levy_foundations_fourierContinuous (μ : FiniteMeasure ℝ) :
    Continuous (LevyFoundations.measureFourier μ) := by sorry
