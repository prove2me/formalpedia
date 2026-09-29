-- Prove2me | Theorems.Thm_lean_workbook_plus_12925
-- name    : lean_workbook_plus_12925
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/32185ede-dc2d-45ce-bc9a-d99acf8d9a3d
-- statement:
--   prove that $6t^5-15t^4+6t^3+6t^2-4t+1 \ge 0$ for $0 \le t \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12925 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 6 * t ^ 5 - 15 * t ^ 4 + 6 * t ^ 3 + 6 * t ^ 2 - 4 * t + 1 ≥ 0   :=  by sorry
