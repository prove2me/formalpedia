-- Prove2me | Theorems.Thm_lean_workbook_plus_50449
-- name    : lean_workbook_plus_50449
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4bf48eab-083d-4eac-8f91-e1b504bc0a5b
-- statement:
--   Prove that $ \left( {1 + \frac{1}{{n + 1}}} \right)^{n + 1} \ge 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50449 : ∀ n : ℕ, (1 + 1 / (n + 1)) ^ (n + 1) ≥ 2   :=  by sorry
