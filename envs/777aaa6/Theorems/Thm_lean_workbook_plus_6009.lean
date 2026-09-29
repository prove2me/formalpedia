-- Prove2me | Theorems.Thm_lean_workbook_plus_6009
-- name    : lean_workbook_plus_6009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6615230f-e469-4e3d-a51d-fefd7f2b9979
-- statement:
--   The inequality $ ab+bc+ca \ge -\frac{1}{2}$ is equivalent to $ 2(ab+bc+ca)+1 \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6009 (a b c: ℝ) : a * b + b * c + c * a ≥ -1 / 2 ↔ 2 * (a * b + b * c + c * a) + 1 ≥ 0   :=  by sorry
