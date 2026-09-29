-- Prove2me | Theorems.Thm_lean_workbook_plus_28385
-- name    : lean_workbook_plus_28385
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/266f5fdd-0090-460a-94d4-6f2fe702a31a
-- statement:
--   Find $ab+bc+ca$ given $a+b+c=11$ and $a^2+b^2+c^2=49$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28385 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36   :=  by sorry
