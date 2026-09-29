-- Prove2me | Theorems.Thm_lean_workbook_plus_38597
-- name    : lean_workbook_plus_38597
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/950544bf-2453-4cf5-b659-82bf986bc1ae
-- statement:
--   $1=a^2b^3c^4\\leq a^{2+2.5}b^{3+1.5}=(ab)^{4.5},$ which says $ab\\geq1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38597 : ∀ a b c : ℝ, 1 = a^2 * b^3 * c^4 → a * b ≥ 1   :=  by sorry
