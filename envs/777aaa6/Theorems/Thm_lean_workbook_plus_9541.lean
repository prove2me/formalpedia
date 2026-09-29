-- Prove2me | Theorems.Thm_lean_workbook_plus_9541
-- name    : lean_workbook_plus_9541
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8246a2f0-f1d0-499c-b222-34f9696e008d
-- statement:
--   Denote by $a$ the word made by the first $29$ boxes in the grid, and by $b$ the word made by the next $61$ boxes in the grid. Then the word representing the grid is $g = (ab)^{22}a$. Since the sum of the numbers in $a$ may be any integer value between $0$ and $29$, the sum of the numbers in the grid may be any integer value between $22\cdot 65 = 1430$ and $22\cdot 65 + 29 = 1459$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9541 {n:ℕ | n = 1430 + k ∧ k <= 29} = {n:ℕ | n >= 1430 ∧ n <= 1459}   :=  by sorry
