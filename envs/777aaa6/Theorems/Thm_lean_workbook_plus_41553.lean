-- Prove2me | Theorems.Thm_lean_workbook_plus_41553
-- name    : lean_workbook_plus_41553
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/84517e63-f117-46d8-8c66-4d4a97f09a21
-- statement:
--   $ab+ac+bc-abc \le 1+ \frac{1}{27}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41553 : ∀ a b c : ℝ, a * b + a * c + b * c - a * b * c ≤ 1 + 1 / 27   :=  by sorry
