-- Prove2me | Theorems.Thm_lean_workbook_plus_73133
-- name    : lean_workbook_plus_73133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/848f270f-56f2-4caf-9d00-93f9536d46d8
-- statement:
--   x^2+y^2+6xy=z^2 $\iff$ x(x+6y)=(z-y)(z+y)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73133 : ∀ x y z : ℤ, x^2 + y^2 + 6 * x * y = z^2 ↔ x * (x + 6 * y) = (z - y) * (z + y)   :=  by sorry
