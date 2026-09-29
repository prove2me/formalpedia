-- Prove2me | Theorems.Thm_lean_workbook_plus_64837
-- name    : lean_workbook_plus_64837
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/93342ceb-12cf-449e-9d6f-6e4ef691beed
-- statement:
--   Prove that $\lfloor x \rfloor + \lfloor 1/x \rfloor \geq 1$ for any $x > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64837 (x : ℝ) (hx : 0 < x) : 1 ≤ floor x + floor (1 / x)   :=  by sorry
