-- Prove2me | Theorems.Thm_lean_workbook_plus_48170
-- name    : lean_workbook_plus_48170
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3822bf5c-357f-4bf0-92b8-0a31835152e6
-- statement:
--   The sum $\sum^{5}_{r=1}\binom{20}{2r-1}$ is easily evaluated
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48170 (h₁ : 0 < 5) : ∑ r in Finset.Icc 1 5, choose 20 (2 * r - 1) = 1024   :=  by sorry
