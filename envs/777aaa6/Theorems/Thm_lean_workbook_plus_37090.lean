-- Prove2me | Theorems.Thm_lean_workbook_plus_37090
-- name    : lean_workbook_plus_37090
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/177d1a96-53b1-4b57-8892-75aa8fbbdece
-- statement:
--   By choosing $y-z=z$ and $x-z=n$ then $y=2z,x=z+n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37090 {x y z : ℤ} (h₁ : x - z = n) (h₂ : y - z = z) : ∃ x y z : ℤ, x = z + n ∧ y = 2 * z   :=  by sorry
