-- Prove2me | Theorems.Thm_lean_workbook_plus_60873
-- name    : lean_workbook_plus_60873
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/004fb70f-ef0a-48de-9ce5-c2ea88756bf9
-- statement:
--   Prove that $(1+x)^n \ge 1+nx$ for all natural numbers $n$ , if you are given that $x>-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60873 (n : ℕ) (x : ℝ) (hx : x > -1) : (1 + x) ^ n ≥ 1 + n * x   :=  by sorry
