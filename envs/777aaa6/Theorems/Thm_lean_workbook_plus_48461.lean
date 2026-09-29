-- Prove2me | Theorems.Thm_lean_workbook_plus_48461
-- name    : lean_workbook_plus_48461
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d03bd15d-4f12-4eb7-81fd-54796b9d0af6
-- statement:
--   For real numbers $a, b, c,$ prove that \n\n $$|a|+|b|+|c|+|a+b+c|\ge |a+b|+|b+c|+|c+a|$$ Old .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48461 (a b c : ℝ) : abs a + abs b + abs c + abs (a + b + c) ≥ abs (a + b) + abs (b + c) + abs (c + a)   :=  by sorry
