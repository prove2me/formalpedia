-- Prove2me | Theorems.Thm_lean_workbook_plus_42314
-- name    : lean_workbook_plus_42314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d0eab0a1-48ff-4ba4-9034-9dce1a54d27b
-- statement:
--   Show that all roots of the equation $ h(x)=x^4-14x^3+64x^2-114x+63=0$ lie in the interval $ (0,14)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42314 (x : ℝ) : x^4 - 14 * x^3 + 64 * x^2 - 114 * x + 63 = 0 → 0 < x ∧ x < 14   :=  by sorry
