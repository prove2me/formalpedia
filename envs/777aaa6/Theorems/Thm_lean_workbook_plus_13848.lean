-- Prove2me | Theorems.Thm_lean_workbook_plus_13848
-- name    : lean_workbook_plus_13848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9aa23ac0-e898-40b6-b677-ba22bc235377
-- statement:
--   Find the minimum value of the function : $1) y=\lvert{x-3}\rvert+\lvert{x}\rvert+\lvert{x+3}\rvert+\lvert{x}+5\rvert$ $2)y=\lvert{x^2+3x+1}\rvert+\lvert{x^2-1}\rvert+\lvert{3x-2}\rvert$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13848 (x : ℝ) : 11 ≤ abs (x - 3) + abs x + abs (x + 3) + abs (x + 5)   :=  by sorry
