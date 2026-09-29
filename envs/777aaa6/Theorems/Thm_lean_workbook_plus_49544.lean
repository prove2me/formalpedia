-- Prove2me | Theorems.Thm_lean_workbook_plus_49544
-- name    : lean_workbook_plus_49544
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b03d2709-3a22-4b1a-a93d-f1e58d71a8bd
-- statement:
--   P5: \nClick to reveal hidden text\n $\binom{3}{1} = 3$ choices for turkey. \n $\binom{5}{2} + \binom{5}{3} = 10 + 10 = 20$ choices for vegetables. \n $\binom{4}{2} = 6$ choices for desserts. \nTherefore $3 \cdot 20 \cdot 6 = 360$ combinations of menus in all.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49544 (Nat.choose 3 1) * (Nat.choose 5 2 + Nat.choose 5 3) * (Nat.choose 4 2) = 360   :=  by sorry
