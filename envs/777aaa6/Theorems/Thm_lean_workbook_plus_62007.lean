-- Prove2me | Theorems.Thm_lean_workbook_plus_62007
-- name    : lean_workbook_plus_62007
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/18d5bcff-15cb-4879-8266-f97a813c5aa5
-- statement:
--   we get that $(1+\frac{a}{n+1})^{n+1}>(1+\frac{a}{n})^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62007 : ∀ n : ℕ, ∀ a : ℝ, (1 + a / (n + 1)) ^ (n + 1) > (1 + a / n) ^ n   :=  by sorry
