-- Prove2me | Theorems.Thm_lean_workbook_plus_49682
-- name    : lean_workbook_plus_49682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/84115124-1eb5-46d7-9db9-144b2074f84c
-- statement:
--   $ \Leftrightarrow (7-2t)^3 \le 3(t^2-1)^2$ which is true for $ t \ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49682 (t : ℝ) (ht : 2 ≤ t) : (7 - 2 * t) ^ 3 ≤ 3 * (t ^ 2 - 1) ^ 2   :=  by sorry
