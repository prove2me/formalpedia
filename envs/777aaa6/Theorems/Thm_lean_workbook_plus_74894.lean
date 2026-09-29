-- Prove2me | Theorems.Thm_lean_workbook_plus_74894
-- name    : lean_workbook_plus_74894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/38c36597-ec42-4191-9585-56efa4a45069
-- statement:
--   So $40x+20727\ge 2(8x^2+4x+3)+1$ , which is $x^2-2x-1295\le 0$ and so $x\in[1,37]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74894  (x : ℕ)
  (h₀ : 0 < x)
  (h₁ : 40 * x + 20727 ≥ 2 * (8 * x^2 + 4 * x + 3) + 1) :
  1 ≤ x ∧ x ≤ 37   :=  by sorry
