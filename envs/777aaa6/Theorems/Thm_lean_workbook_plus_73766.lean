-- Prove2me | Theorems.Thm_lean_workbook_plus_73766
-- name    : lean_workbook_plus_73766
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b3d34cf5-36bf-4990-91d5-29ba37fcf462
-- statement:
--   Given $x^2 + xy = 28$ and $y^2 + xy = -12$, find $(x+y)(x-y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73766 (x y : ℝ) (h₁ : x^2 + x*y = 28) (h₂ : y^2 + x*y = -12) : (x + y)*(x - y) = 40   :=  by sorry
