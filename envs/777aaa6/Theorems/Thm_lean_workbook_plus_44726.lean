-- Prove2me | Theorems.Thm_lean_workbook_plus_44726
-- name    : lean_workbook_plus_44726
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ea49d1b6-11ee-4b16-b1a0-87f6bb081c57
-- statement:
--   Prove that $xz^5+x^5y+y^5z\geq \frac{1}{3}(xy^2+yz^2+x^2z)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44726 : ∀ x y z : ℝ, x * z ^ 5 + x ^ 5 * y + y ^ 5 * z ≥ (1 / 3) * (x * y ^ 2 + y * z ^ 2 + x ^ 2 * z) ^ 2   :=  by sorry
