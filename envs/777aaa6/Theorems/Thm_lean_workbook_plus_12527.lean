-- Prove2me | Theorems.Thm_lean_workbook_plus_12527
-- name    : lean_workbook_plus_12527
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/396b1fb2-b606-4f61-8427-61ff5b784864
-- statement:
--   Prove the inequality\n\n$x^3+2xy^2+y^3+2yz^2+z^3+2zx^2\geq 3(x^2y+y^2z+z^2x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12527 : ∀ x y z : ℝ, x^3 + 2 * x * y^2 + y^3 + 2 * y * z^2 + z^3 + 2 * z * x^2 ≥ 3 * (x^2 * y + y^2 * z + z^2 * x)   :=  by sorry
