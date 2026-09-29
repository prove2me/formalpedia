-- Prove2me | Theorems.Thm_lean_workbook_plus_13428
-- name    : lean_workbook_plus_13428
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/eb832ce0-f166-429c-8071-15eabca0ef3f
-- statement:
--   Prove that if $a$ , $b$ , $c$ , $d$ , $e$ , and $f$ are real numbers, \n $$\sqrt{(a-c)^2+(b-d)^2}+\sqrt{(c-e)^2+(d-f)^2}\geq\sqrt{(e-a)^2+(f-b)^2}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13428 (a b c d e f : ℝ) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) + Real.sqrt ((a - e) ^ 2 + (b - f) ^ 2) ≥ Real.sqrt ((e - a) ^ 2 + (f - b) ^ 2)   :=  by sorry
