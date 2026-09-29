-- Prove2me | Theorems.Thm_lean_workbook_plus_19090
-- name    : lean_workbook_plus_19090
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c7a01b9e-2d6e-4045-9746-ec266a6311da
-- statement:
--   If $ f(x) = \frac {\left(6x^2 + x + 2\right)^3}{27}$ , then $ f(1) = \frac {\left(6 + 1 + 2\right)^3}{27} = \boxed{27}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19090 (f : ℝ → ℝ) (f_def : ∀ x, f x = (6 * x ^ 2 + x + 2) ^ 3 / 27) : f 1 = 27   :=  by sorry
