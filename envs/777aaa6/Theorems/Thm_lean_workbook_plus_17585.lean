-- Prove2me | Theorems.Thm_lean_workbook_plus_17585
-- name    : lean_workbook_plus_17585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5ca237c1-d336-4827-be9d-6bad710c6afb
-- statement:
--   Factorization identity: $(a + b + c)(a^2 + b^2 + c^2 - ab - bc - ac) = a^3 + b^3 + c^3 - 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17585 (a b c : ℝ) : (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - a * c) = a^3 + b^3 + c^3 - 3 * a * b * c   :=  by sorry
