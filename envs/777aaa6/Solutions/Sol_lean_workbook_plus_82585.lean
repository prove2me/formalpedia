-- Prove2me | solution 1 for lean_workbook_plus_82585
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:43.532701+00:00
-- url     : https://prove2.me/submissions/c2cf25e5-a2f6-428c-b56d-a26cb10371f7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ¬ (∀ (f : ℝ → ℝ), f 1 = 0 →
    (∀ x, f (x - 1) + f x = 1) → ∀ x, f x = 1 - x) := by
  intro h
  let f : ℝ → ℝ := fun x => if ⌊x⌋ % 2 = 0 then 1 else 0
  have hf : f 1 = 0 := by norm_num [f]
  have hp : ∀ x, f (x - 1) + f x = 1 := by
    intro x
    dsimp [f]
    rw [Int.floor_sub_one]
    split_ifs <;> norm_num <;> omega
  have hbad := h f hf hp 2
  norm_num [f] at hbad
