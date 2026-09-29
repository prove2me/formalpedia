-- Prove2me | Theorems.Thm_lean_workbook_plus_68083
-- name    : lean_workbook_plus_68083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/1c9c81d2-5fc7-45e6-a368-d4f51424e284
-- statement:
--   For $x>0$ , we have $\displaystyle \frac{x}{4+x^2} \leq \frac{1}{20}\left(1+\frac{15}{1+x}\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68083 (x : ℝ) (hx : 0 < x) : (x / (4 + x ^ 2) ≤ (1 / 20) * (1 + 15 / (1 + x)))   :=  by sorry
