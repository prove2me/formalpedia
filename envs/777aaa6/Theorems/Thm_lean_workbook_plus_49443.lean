-- Prove2me | Theorems.Thm_lean_workbook_plus_49443
-- name    : lean_workbook_plus_49443
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e2dd45ba-9d90-487a-923f-a42a4d44c225
-- statement:
--   Prove that $\frac{1}{1999}<\prod_{n=1}^{999} \frac{2n-1}{2n}<\frac{1}{44}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49443 : (1 / 1999 : ℝ) < ∏ n in Finset.range 999, (2 * n - 1) / (2 * n) ∧ ∏ n in Finset.range 999, (2 * n - 1) / (2 * n) < 1 / 44   :=  by sorry
