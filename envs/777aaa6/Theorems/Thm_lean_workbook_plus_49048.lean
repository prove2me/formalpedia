-- Prove2me | Theorems.Thm_lean_workbook_plus_49048
-- name    : lean_workbook_plus_49048
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f3bdfa75-81d9-4e0a-8051-5dfc450f4e0a
-- statement:
--   By Am-Gm we have $2\sqrt{x(y^{29}+z^{2007})}\leq x+y^{29}+z^{2007}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49048 : ∀ x y z : ℝ, 2 * Real.sqrt (x * (y^29 + z^2007)) ≤ x + y^29 + z^2007   :=  by sorry
