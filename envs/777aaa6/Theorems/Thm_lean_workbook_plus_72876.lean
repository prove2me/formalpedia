-- Prove2me | Theorems.Thm_lean_workbook_plus_72876
-- name    : lean_workbook_plus_72876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/12596151-be41-41b4-bd5b-687ed983c787
-- statement:
--   $ \frac{1}{3}xyz \ge \sqrt{3} \Longrightarrow xyz \ge 3\sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72876 (x y z : ℝ) (h : 1/3 * x * y * z ≥ Real.sqrt 3) : x * y * z ≥ 3 * Real.sqrt 3   :=  by sorry
