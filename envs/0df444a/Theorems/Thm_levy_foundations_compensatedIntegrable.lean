-- Prove2me | Theorems.Thm_levy_foundations_compensatedIntegrable
-- name    : levy_foundations_compensatedIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:35:14.629692+00:00
-- url     : https://prove2.me/theorems/473d7e84-9aca-431c-926c-e65ba28288e4
-- title:
--   Bochner integrability of the compensated jump integrand
-- statement:
--   For any fixed Fourier frequency, compensation of the linear small-jump term makes the complex-valued Lévy–Khintchine jump integrand Bochner integrable against a Lévy measure.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L80-L160. Analytic integrability used to define the exponent. The new Prove2Me theorem requires its own accepted proof and statement audit.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_compensatedIntegrand

open MeasureTheory

theorem levy_foundations_compensatedIntegrable (ν : Measure ℝ)
    (hν : LevyFoundations.isLevyMeasure ν) (ξ : ℝ) :
    Integrable (LevyFoundations.compensatedIntegrand ξ) ν := by
  sorry
