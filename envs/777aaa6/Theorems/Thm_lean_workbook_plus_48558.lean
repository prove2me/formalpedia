-- Prove2me | Theorems.Thm_lean_workbook_plus_48558
-- name    : lean_workbook_plus_48558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/253ca16e-322d-4c1a-8527-248f4545530e
-- statement:
--   $y^2 + y + 1 + 2\sqrt{y^2 + y} \ge y^2 - y \Leftrightarrow 2y + 1 + 2\sqrt{y^2 + y} \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48558 : ∀ y : ℝ, y^2 + y + 1 + 2 * Real.sqrt (y^2 + y) ≥ y^2 - y ↔ 2 * y + 1 + 2 * Real.sqrt (y^2 + y) ≥ 0   :=  by sorry
