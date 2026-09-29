-- Prove2me | Theorems.Thm_lean_workbook_plus_1680
-- name    : lean_workbook_plus_1680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4ab9b211-9ea4-49cd-b997-941d9be7d265
-- statement:
--   Let the series be $a+ar+ar^2+ar^3...=S$. Prove that $S=\frac{a}{1-r}$ when $|r|<1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1680 (a r : ℝ) (h : |r| < 1) : ∑' i : ℕ, a * r ^ i = a / (1 - r)   :=  by sorry
