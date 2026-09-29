-- Prove2me | Theorems.Thm_lean_workbook_plus_78010
-- name    : lean_workbook_plus_78010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ee2d2fe1-5820-4d98-92be-3b208d76447c
-- statement:
--   Prove that $X + \frac{1}{X} \ge 2$ for all $x > 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78010 (x : ℝ) (hx: x > 0) : x + (1/x) ≥ 2   :=  by sorry
