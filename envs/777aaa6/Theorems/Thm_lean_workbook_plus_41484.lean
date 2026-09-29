-- Prove2me | Theorems.Thm_lean_workbook_plus_41484
-- name    : lean_workbook_plus_41484
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7bc55428-b26e-44a4-ada2-7aad86461919
-- statement:
--   We also know that $q = a^2 bc + a b^2 c + abc^2 = (abc)(a+b+c)$ , and Vieta's on the first polynomial yields $abc=1$ , $a+b+c = -3$ , so $q = -3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41484  (a b c : ℝ)
  (h₀ : a + b + c = -3)
  (h₁ : a * b * c = 1)
  (h₂ : q = a^2 * b * c + a * b^2 * c + a * b * c^2) :
  q = -3   :=  by sorry
