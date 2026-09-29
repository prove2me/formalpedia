-- Prove2me | Theorems.Thm_lean_workbook_plus_52875
-- name    : lean_workbook_plus_52875
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/eba97071-3dd8-4b3c-8e9a-bc24ef1816af
-- statement:
--   I forgot how many pilgrims came on the Mayflower. Fortunately, I have a clue. $5x+52=-3x+1012$ where x is the number of pilgrims. How many pilgrims came?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52875 (x : ℕ) (h : 5 * x + 52 = 1012 - 3 * x) : x = 120   :=  by sorry
