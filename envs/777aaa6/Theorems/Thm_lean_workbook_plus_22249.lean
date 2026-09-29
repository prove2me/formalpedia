-- Prove2me | Theorems.Thm_lean_workbook_plus_22249
-- name    : lean_workbook_plus_22249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e56d2433-1d6e-41d6-b5f7-ebed82a41283
-- statement:
--   If \(y \ge 3\), then \(y+z = x + 2y + 1\), so \(z = x + y +1\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22249  (x y z : ℝ)
  (h₀ : y ≥ 3)
  (h₁ : y + z = x + 2 * y + 1) :
  z = x + y + 1   :=  by sorry
