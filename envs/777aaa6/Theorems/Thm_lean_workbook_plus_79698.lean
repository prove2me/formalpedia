-- Prove2me | Theorems.Thm_lean_workbook_plus_79698
-- name    : lean_workbook_plus_79698
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/39c5f1ca-851b-4a88-b73e-a82ce2263bf5
-- statement:
--   Prove that \(x+y+xy/(\sqrt{x}+\sqrt{y})^2 \ge 9\sqrt{xy}/4\) for \(x, y > 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79698 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x + y + x * y / (Real.sqrt x + Real.sqrt y) ^ 2 ≥ 9 * Real.sqrt (x * y) / 4   :=  by sorry
