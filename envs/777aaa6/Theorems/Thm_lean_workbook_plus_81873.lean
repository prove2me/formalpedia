-- Prove2me | Theorems.Thm_lean_workbook_plus_81873
-- name    : lean_workbook_plus_81873
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/13e52fa0-d559-4653-a74c-31bdb342d281
-- statement:
--   Let $ x,y,z \ge 0$ and $ x \le y+z$ , then $ \frac{x}{1+x} \le \frac{y}{1+y} + \frac{z}{1+z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81873 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ≤ y + z) : x / (1 + x) ≤ y / (1 + y) + z / (1 + z)   :=  by sorry
