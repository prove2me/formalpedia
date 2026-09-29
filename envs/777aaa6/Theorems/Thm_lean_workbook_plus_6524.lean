-- Prove2me | Theorems.Thm_lean_workbook_plus_6524
-- name    : lean_workbook_plus_6524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/17b67657-349b-4e61-b29e-e5c6a25186c8
-- statement:
--   Let $a$ and $b$ be real numbers such that $3\le a^2+ab+b^2\le6$ . Prove that $2\le a^4+b^4\le72 .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6524 (a b : ℝ) (h1 : 3 ≤ a ^ 2 + b ^ 2 + a * b) (h2 : a ^ 2 + b ^ 2 + a * b ≤ 6) : 2 ≤ a ^ 4 + b ^ 4 ∧ a ^ 4 + b ^ 4 ≤ 72   :=  by sorry
