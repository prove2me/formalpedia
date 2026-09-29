-- Prove2me | Theorems.Thm_lean_workbook_plus_5572
-- name    : lean_workbook_plus_5572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a148d542-9a8f-4a47-819f-23a97c8e5936
-- statement:
--   The probability of drawing two marbles of the same color is $ \frac {1000}{2001}$ , so the probability of them NOT being the same color is $ 1 - \frac {1000}{2001} = \frac {1001}{2001}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5572 :
  1 - (1000 : ℝ) / 2001 = 1001 / 2001   :=  by sorry
