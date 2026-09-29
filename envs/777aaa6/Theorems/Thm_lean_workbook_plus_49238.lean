-- Prove2me | Theorems.Thm_lean_workbook_plus_49238
-- name    : lean_workbook_plus_49238
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8cd09f90-b91d-48aa-b5ff-77d5179bd123
-- statement:
--   First, we have $(a^2+b^2)(b^2+c^2)(c^2+a^2) \ge \frac{1}{2}[(a+b)(b+c)(c+a)-4abc]^2. \quad (1)$ It's by Cauchy-Schwarz.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49238 : ∀ a b c : ℝ, (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (1/2)*((a + b) * (b + c) * (c + a) - 4 * a * b * c)^2   :=  by sorry
