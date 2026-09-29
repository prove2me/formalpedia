-- Prove2me | Theorems.Thm_lean_workbook_plus_8155
-- name    : lean_workbook_plus_8155
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/86ff4081-e5d7-493f-b6a1-4cefc8eb40d0
-- statement:
--   Let $f(x)$ be a linear polynomial. If $f(0) = 3$ and $f(1) = 2023$ , find $f(-10)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8155 (f : ℤ → ℤ) (hf : ∃ a b, ∀ x, f x = a * x + b) : f 0 = 3 ∧ f 1 = 2023 → f (-10) = -20197   :=  by sorry
