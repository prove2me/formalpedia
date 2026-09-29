-- Prove2me | Theorems.Thm_lean_workbook_plus_44381
-- name    : lean_workbook_plus_44381
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/87219995-cee1-410f-812c-3c28b289155c
-- statement:
--   Calculate $2^{log_ {6}18} . 3^{log_{6}3}$ in decimal form.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44381 (x : ℝ) (hx : x = 2^Real.logb 6 18 * 3^Real.logb 6 3) : x = 6   :=  by sorry
