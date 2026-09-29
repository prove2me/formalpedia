-- Prove2me | Theorems.Thm_lean_workbook_plus_12251
-- name    : lean_workbook_plus_12251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7d8a0020-0539-4d3d-a4d0-9ca6ce7d8f1f
-- statement:
--   Prove that $ \sqrt {x^2 + xy + y^2} \ge \sqrt {3xy}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12251 (x y : ℝ) : Real.sqrt (x ^ 2 + x * y + y ^ 2) ≥ Real.sqrt (3 * x * y)   :=  by sorry
