-- Prove2me | Theorems.Thm_lean_workbook_plus_54844
-- name    : lean_workbook_plus_54844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/08840c50-7998-43d8-aa18-eab7999d8a82
-- statement:
--   Let $a = xy$ , $b = x-y$ . Then, $a + b + 1 = ab - 2 \Longleftrightarrow (a-1)(b-1) = 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54844 (a b: ℤ) : a + b + 1 = a * b - 2 ↔ (a-1) * (b-1) = 4   :=  by sorry
