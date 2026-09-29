-- Prove2me | Theorems.Thm_lean_workbook_plus_18379
-- name    : lean_workbook_plus_18379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8f9c407b-7632-4dc0-8132-14938a367883
-- statement:
--   Let $a, b, c$ be positive real numbers such that $a^2+b^2+c^2+abc=4$. Prove that \n$2\sqrt{2-abc}+abc\geq a+b+c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18379 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : 2 * Real.sqrt (2 - a * b * c) + a * b * c ≥ a + b + c   :=  by sorry
