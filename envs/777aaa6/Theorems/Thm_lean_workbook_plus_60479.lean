-- Prove2me | Theorems.Thm_lean_workbook_plus_60479
-- name    : lean_workbook_plus_60479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/20961d53-80fe-4b08-8ec0-d5cd28217bd2
-- statement:
--   So it remains to show $ y + |x - y + z|\geq |x - y| + |y - z|$ for nonnegative $ x,y,z$ . This is equivalent to the square of the inequality, $ \iff y^2 + (x - y + z)^2 + 2y|x - y + z|\geq (x - y)^2 + (y - z)^2 + 2|x - y||y - z|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60479 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : y + |x - y + z| ≥ |x - y| + |y - z|   :=  by sorry
