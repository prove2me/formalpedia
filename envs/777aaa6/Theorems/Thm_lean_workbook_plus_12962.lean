-- Prove2me | Theorems.Thm_lean_workbook_plus_12962
-- name    : lean_workbook_plus_12962
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/71df3bb8-4799-4218-8433-5554c4569223
-- statement:
--   Prove that the inequality $125b(3-b)+\dfrac {(3-b)^2(125b+\dfrac{525} 2)} 4\le 666$ holds for $b\le 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12962 (b : ℝ) (hb : b ≤ 3) :
  125 * b * (3 - b) + (3 - b) ^ 2 * (125 * b + 525 / 2) / 4 ≤ 666   :=  by sorry
