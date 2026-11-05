-- Prove2me | Theorems.Thm_levy_foundations_levyMeasure_measure_setOf_abs_ge_lt_top
-- name    : levy_foundations_levyMeasure_measure_setOf_abs_ge_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:44:10.454219+00:00
-- url     : https://prove2.me/theorems/b8e5f533-30f3-4a2a-8140-62aadccd1e65
-- title:
--   Finite Lévy intensity away from the origin
-- statement:
--   Finite Lévy intensity away from the origin. Adapted from the frozen LeanLevy public theorem with its measure-theoretic assumptions intact.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L71

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory ENNReal Set
open scoped NNReal ENNReal

theorem levy_foundations_levyMeasure_measure_setOf_abs_ge_lt_top
    {ν : Measure ℝ} (hν : LevyFoundations.isLevyMeasure ν)
    {ε : ℝ} (hε : 0 < ε) : ν {x | ε ≤ |x|} < ⊤ := by sorry
