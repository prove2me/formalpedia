-- Prove2me | Theorems.Thm_lean_workbook_plus_3613
-- name    : lean_workbook_plus_3613
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1029cb9c-3cdd-493b-8bdf-4c8851634e5e
-- statement:
--   By Cauchy-Schwarz\n$(x+y+z)(xy^3+yz^3+zx^3) =\left(\sum (\sqrt{z})^2\right)\left(\sum (\sqrt{xy^3})^2\right) \ge \left(\sum \sqrt{xy^3z}\right)^2 = xyz(x+y+z)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3613 : ∀ x y z : ℝ, (x + y + z) * (x * y ^ 3 + y * z ^ 3 + z * x ^ 3) ≥ x * y * z * (x + y + z) ^ 2   :=  by sorry
