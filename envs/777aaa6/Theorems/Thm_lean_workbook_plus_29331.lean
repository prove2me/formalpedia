-- Prove2me | Theorems.Thm_lean_workbook_plus_29331
-- name    : lean_workbook_plus_29331
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/78532f7f-6b47-439d-bd4a-f6318e6bd4da
-- statement:
--   Given $a+b+c=\frac{\pi}{2}$, prove that $[tg(a)]^2+[tg(b)]^2+[tg(c)]^2\ge1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29331 : ∀ a b c : ℝ, a + b + c = π / 2 → (tan a)^2 + (tan b)^2 + (tan c)^2 >= 1   :=  by sorry
