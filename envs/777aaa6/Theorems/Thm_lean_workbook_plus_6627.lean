-- Prove2me | Theorems.Thm_lean_workbook_plus_6627
-- name    : lean_workbook_plus_6627
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/22d9f302-3c06-40a9-8176-a1c9ab34e0be
-- statement:
--   If they're arranged in a $2\times2$ grid, then we maximize $xy$ given $3x+3y=120$ , or $x+y=40$ . At $x=y=20$ , this gives us $\boxed{400}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6627  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : 3 * x + 3 * y = 120)
  (h₂ : x + y = 40) :
  x * y ≤ 400   :=  by sorry
