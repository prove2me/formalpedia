-- Prove2me | Theorems.Thm_lean_workbook_plus_18929
-- name    : lean_workbook_plus_18929
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/044a25df-6cfb-47e7-974a-2ab1e19c82c0
-- statement:
--   Prove that $\cos (\frac{\pi}{4}) + \cos (\frac{3 \pi}{4}) + \cos (\frac{5 \pi}{4}) + \cos (\frac{7 \pi}{4}) = \frac{1}{\sqrt{2}} + (- \frac{1}{\sqrt{2}}) + (-1) + (- \frac{1}{\sqrt{2}}) + \frac{1}{\sqrt{2}} = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18929  : Real.cos (π / 4) + Real.cos (3 * π / 4) + Real.cos (5 * π / 4) + Real.cos (7 * π / 4) = 0   :=  by sorry
