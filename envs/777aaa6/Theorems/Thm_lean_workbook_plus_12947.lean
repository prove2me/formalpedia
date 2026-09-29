-- Prove2me | Theorems.Thm_lean_workbook_plus_12947
-- name    : lean_workbook_plus_12947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/760fcf0e-aea4-4308-886d-4afedf1ed262
-- statement:
--   Given the expression \(n*(n-1)*(n-2)\), prove that it is divisible by 3 for \(n \geq 3\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12947 (n : ℕ) (h₁ : n ≥ 3) : 3 ∣ n * (n - 1) * (n - 2)   :=  by sorry
