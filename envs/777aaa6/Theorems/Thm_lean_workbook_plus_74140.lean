-- Prove2me | Theorems.Thm_lean_workbook_plus_74140
-- name    : lean_workbook_plus_74140
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/eef41226-9950-4ac2-9c4b-84074ba3c0a4
-- statement:
--   Prove that $ \frac{1}{x+y}\leq \frac{1}{4}\left(\frac{1}{x}+\frac{1}{y}\right)$ for all $x, y > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74140 (x y : ℝ) (hx : x > 0) (hy : y > 0) : 1 / (x + y) ≤ (1 / 4) * (1 / x + 1 / y)   :=  by sorry
