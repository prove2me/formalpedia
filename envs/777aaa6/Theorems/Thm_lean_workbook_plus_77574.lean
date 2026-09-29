-- Prove2me | Theorems.Thm_lean_workbook_plus_77574
-- name    : lean_workbook_plus_77574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1a31a1a7-e420-4231-a4d4-2e651f665581
-- statement:
--   Prove that $n=1\cdot 84\equiv 0\bmod 2$ and $5|n$ implies $10|n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77574 (n : ℕ) (h₁ : n ≡ 0 [ZMOD 2]) (h₂ : 5 ∣ n) : 10 ∣ n   :=  by sorry
