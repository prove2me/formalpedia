-- Prove2me | Theorems.Thm_lean_workbook_plus_52216
-- name    : lean_workbook_plus_52216
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/dc2b6965-5c6e-412d-8ccb-de6226e60a4a
-- statement:
--   Additional sum-to-product identity: $\cos(a) + \cos(b) = 2\cos \left( \frac{a+b}{2} \right) \cos \left( \frac{a-b}{2} \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52216 : ∀ a b : ℝ, cos a + cos b = 2 * cos (a + b) / 2 * cos (a - b) / 2   :=  by sorry
