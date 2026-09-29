-- Prove2me | Theorems.Thm_lean_workbook_plus_8684
-- name    : lean_workbook_plus_8684
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6a8be0dc-b86a-48cc-8d06-3f5f68f815e2
-- statement:
--   Calculate the infinite series: $ \sum_{n=1}^{\infty}\frac{n}{3^n} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8684 (x : ℝ) : ∑' n : ℕ, (n / 3 ^ n) = 3 / 4   :=  by sorry
