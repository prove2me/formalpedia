-- Prove2me | Theorems.Thm_lean_workbook_plus_50878
-- name    : lean_workbook_plus_50878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d8b0368c-e692-4a32-8068-7f71cfae3de5
-- statement:
--   Prove that $ 3\left(a^2 + b^2 + c^2\right)\geq a^2 + b^2 + c^2 + 2(\text{ab} + \text{bc} + \text{ca})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50878 : ∀ a b c : ℝ, 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a)   :=  by sorry
