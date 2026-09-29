-- Prove2me | Theorems.Thm_lean_workbook_plus_30415
-- name    : lean_workbook_plus_30415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a3b71eb6-f13c-46c7-b2bb-4c937e502f3f
-- statement:
--   prove $ \frac{a^3+b^3+c^3}{3}\geq abc+\frac{3}{4}|(a-b)(b-c)(c-a)|$ given $ a,b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30415 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^3 + b^3 + c^3) / 3 ≥ a * b * c + (3 / 4) * |(a - b) * (b - c) * (c - a)|   :=  by sorry
