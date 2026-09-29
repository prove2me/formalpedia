-- Prove2me | Theorems.Thm_lean_workbook_plus_55746
-- name    : lean_workbook_plus_55746
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1cbe41d7-955a-436d-a0c4-3c9fd21b2d6d
-- statement:
--   $ab+bc+ca-abc\le\frac{28}{27}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55746 : ∀ a b c : ℝ, a * b + b * c + c * a - a * b * c ≤ 28 / 27   :=  by sorry
