-- Prove2me | Theorems.Thm_levy_foundations_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- name    : levy_foundations_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:49:59.348978+00:00
-- url     : https://prove2.me/theorems/3a72a393-f042-4c7a-a116-e6e839218b2d
-- title:
--   Equality extends from dense rational times by right-continuity
-- statement:
--   Equality extends from dense rational times by right-continuity.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L180

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Definitions.Def_levy_foundations_ceilApprox

open Filter Topology
open scoped NNReal

theorem levy_foundations_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
    {β : Type*} [TopologicalSpace β] [T2Space β]
    {f g : ℝ≥0 → β}
    (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hg : Continuous g)
    (heq : ∀ (k n : ℕ),
      f ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) =
      g ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))) :
    f = g := by sorry
