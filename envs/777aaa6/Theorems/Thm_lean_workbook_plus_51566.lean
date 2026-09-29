-- Prove2me | Theorems.Thm_lean_workbook_plus_51566
-- name    : lean_workbook_plus_51566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/bd930a68-1948-4133-b75d-769d63830161
-- statement:
--   b) Sub in $s=0$ \n $0=-4.9t^{2}+20t$ \n $-4.9t\left(t-\frac{200}{49}\right)=0$ \n $t=0,\frac{200}{49}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51566  (t : ℝ)
  (h₀ : -4.9 * t^2 + 20 * t = 0) :
  t = 0 ∨ t = 200 / 49   :=  by sorry
