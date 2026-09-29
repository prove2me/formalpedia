-- Prove2me | Theorems.Thm_lean_workbook_plus_41163
-- name    : lean_workbook_plus_41163
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ce05ef9b-4503-49ff-b3fa-53cd9e5f201e
-- statement:
--   Use the inequality $\frac{1}{1+t^2} \le \frac{27(2-t)}{50}$ for all $t \le 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41163 : ∀ t : ℝ, t ≤ 1 → 1 / (1 + t ^ 2) ≤ 27 * (2 - t) / 50   :=  by sorry
