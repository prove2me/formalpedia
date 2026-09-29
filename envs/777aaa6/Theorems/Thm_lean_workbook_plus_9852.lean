-- Prove2me | Theorems.Thm_lean_workbook_plus_9852
-- name    : lean_workbook_plus_9852
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bfd4784c-1b9c-42e5-9e7f-df172e3b6edc
-- statement:
--   Prove that for $ a+b+c=3$ and $ x=\frac{3}{2}$, $ ab^{x}+bc^{x}+ca^{x}\leq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9852 (a b c : ℝ) (hx : x = 3/2) (hab : a + b + c = 3) : a * b ^ x + b * c ^ x + c * a ^ x ≤ 3   :=  by sorry
