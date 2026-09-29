-- Prove2me | Theorems.Thm_lean_workbook_plus_26796
-- name    : lean_workbook_plus_26796
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a248188d-196b-447e-813e-60d83738e93b
-- statement:
--   c)[Total number of ways to choose 5 players out of 12 ] - [number of ways in which lebron and james are playing together are\n$\binom{12-2}{5-2}$ or $\binom{10}{3}$ ways]= $\binom{12}{5}$ - $\binom{10}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26796 (Nat.choose 12 5) - (Nat.choose 10 3) = 564   :=  by sorry
