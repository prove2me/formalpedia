-- Prove2me | Theorems.Thm_lean_workbook_plus_9423
-- name    : lean_workbook_plus_9423
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5c4f1abe-36d5-423d-9891-22038b1697b6
-- statement:
--   We have $\frac{1}{a}+\frac{1}{b}=\frac{a+b}{ab}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9423  (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0) :
  1 / a + 1 / b = (a + b) / (a * b)   :=  by sorry
