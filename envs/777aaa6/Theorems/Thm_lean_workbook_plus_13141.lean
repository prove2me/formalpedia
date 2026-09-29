-- Prove2me | Theorems.Thm_lean_workbook_plus_13141
-- name    : lean_workbook_plus_13141
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/fa526f63-a211-4df6-aac8-941dca2f6937
-- statement:
--   Factorize we get: \n\n $Q=\frac{1}{a+b+c}\left(\frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}\right)=\frac{1}{abc\left(a+b+c\right)}\left(a+b+c\right)=\frac{1}{abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13141  (a b c : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
  (h₁ : a + b + c = 1) :
  1 / (a * b * c * (a + b + c)) * (a + b + c) = 1 / (a * b * c)   :=  by sorry
