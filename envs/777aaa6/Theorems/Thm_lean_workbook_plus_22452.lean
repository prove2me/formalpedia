-- Prove2me | Theorems.Thm_lean_workbook_plus_22452
-- name    : lean_workbook_plus_22452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/32b6a8de-4443-4525-ade7-a8f5c5f878db
-- statement:
--   Prove that $(a^2+b^2+c^2-ab-bc-ac) \geq 0$ for any real numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22452 (a b c: ℝ): a^2 + b^2 + c^2 - a * b - b * c - a * c ≥ 0   :=  by sorry
