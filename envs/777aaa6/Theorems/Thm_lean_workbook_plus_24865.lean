-- Prove2me | Theorems.Thm_lean_workbook_plus_24865
-- name    : lean_workbook_plus_24865
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/85c3751d-d7b3-4c75-9318-9d55e5c195df
-- statement:
--   Prove that $\frac{3k-2}{k!} = \frac{3}{(k-1)!} - \frac{2}{k!}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24865 : ∀ k, (3 * k - 2) / k! = 3 / (k - 1)! - 2 / k!   :=  by sorry
