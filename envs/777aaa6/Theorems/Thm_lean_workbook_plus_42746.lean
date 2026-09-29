-- Prove2me | Theorems.Thm_lean_workbook_plus_42746
-- name    : lean_workbook_plus_42746
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/63d49da8-7861-4929-a46f-12a42d5cc641
-- statement:
--   $ a(1-a)(3-2b)+b(1-b)(3-2a) \ge 0 $ true for $0\le a,b \le 1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42746 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : a * (1 - a) * (3 - 2 * b) + b * (1 - b) * (3 - 2 * a) ≥ 0   :=  by sorry
