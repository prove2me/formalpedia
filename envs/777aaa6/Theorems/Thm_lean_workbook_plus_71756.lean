-- Prove2me | Theorems.Thm_lean_workbook_plus_71756
-- name    : lean_workbook_plus_71756
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2a63ced2-015a-4cd9-932d-8342aa8d90cc
-- statement:
--   By triangle inequalities again, $\log_{10}(12n)> \log_{10}(75)\implies n>6$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71756  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Real.logb 10 (12 * n) > Real.logb 10 75) :
  n > 6   :=  by sorry
