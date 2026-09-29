-- Prove2me | Theorems.Thm_lean_workbook_plus_39448
-- name    : lean_workbook_plus_39448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d1d1481b-5d4b-44cf-ac85-906382d4f73b
-- statement:
--   Let $x = a-b$ and $y = b-c$. Then $(a-b)(b-c)(c-a) = -xy(x+y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39448 (a b c x y : ℝ) (h₁ : x = a - b) (h₂ : y = b - c) : (a - b) * (b - c) * (c - a) = -x * y * (x + y)   :=  by sorry
