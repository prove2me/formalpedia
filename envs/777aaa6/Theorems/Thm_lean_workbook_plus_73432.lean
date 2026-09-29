-- Prove2me | Theorems.Thm_lean_workbook_plus_73432
-- name    : lean_workbook_plus_73432
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d5f65e8e-4a7b-4fa2-991e-50d3dfbeabc3
-- statement:
--   Prove that for all integers $n = 0, 1, 2, ...$ , the following equality holds: $\lfloor \frac{1+\lfloor \frac {1+na^2}{a}\rfloor} {a} \rfloor=n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73432 : ∀ (n : ℕ), ∀ (a : ℝ), (a > 0 ∧ a < 1) → ⌊(1 + ⌊(1 + n * a ^ 2)/a⌋)/a⌋ = n   :=  by sorry
