-- Prove2me | Theorems.Thm_lean_workbook_plus_36970
-- name    : lean_workbook_plus_36970
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/937b139b-b0ca-4619-9c42-8cdbce539518
-- statement:
--   Prove the following inequality: $2(xy+yz+zx)-(x^2 +y^2 +z^2) \le 3 \ \ ; $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36970 : ∀ x y z : ℝ, 2 * (x * y + y * z + z * x) - (x ^ 2 + y ^ 2 + z ^ 2) ≤ 3   :=  by sorry
