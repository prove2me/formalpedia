-- Prove2me | Theorems.Thm_lean_workbook_plus_950
-- name    : lean_workbook_plus_950
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/9b5e4440-e016-4e7a-b3fd-f669ea653a8d
-- statement:
--   Find $ k $ such that $ x=ky $ where $ \frac{k^3}{4}=\frac{7k}{3} $ where $ k>0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_950 (k : ℝ) (h₁ : k > 0) (h₂ : k^3 / 4 = 7 * k / 3) : k = Real.sqrt (28 / 3)   :=  by sorry
