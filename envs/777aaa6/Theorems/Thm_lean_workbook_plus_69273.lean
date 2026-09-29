-- Prove2me | Theorems.Thm_lean_workbook_plus_69273
-- name    : lean_workbook_plus_69273
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/441f2395-e34d-4a3a-9f9e-b8fbe9c9c7ba
-- statement:
--   Demonstrate the rule: $a | (am+b)^n - b^n$ for $a, m, b, n \in \mathbb{N}$ and $0 \le b < a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69273 (a m b n : ℕ) (h₀ : 0 < n) (h₁ : 0 < a) (h₂ : 0 < b) (h₃ : b < a) :
  a ∣ (a*m + b)^n - b^n   :=  by sorry
