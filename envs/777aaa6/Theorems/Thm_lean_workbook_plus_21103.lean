-- Prove2me | Theorems.Thm_lean_workbook_plus_21103
-- name    : lean_workbook_plus_21103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b42460ea-7de1-4a47-b119-20e84e916484
-- statement:
--   $ s > 0$ ,and $ t > 0$ , $ 4st \le (s + t)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21103 (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : 4 * s * t ≤ (s + t) ^ 2   :=  by sorry
