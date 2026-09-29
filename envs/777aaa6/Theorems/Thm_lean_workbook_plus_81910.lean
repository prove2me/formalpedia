-- Prove2me | Theorems.Thm_lean_workbook_plus_81910
-- name    : lean_workbook_plus_81910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c81fcd99-25fa-4d05-860e-e149fda89466
-- statement:
--   Prove that: $\frac{1}{4-x^2} \leq \frac{x^4+5}{18}$ with $x^2<2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81910 : ∀ x : ℝ, x^2 < 2 → 1 / (4 - x^2) ≤ (x^4 + 5) / 18   :=  by sorry
