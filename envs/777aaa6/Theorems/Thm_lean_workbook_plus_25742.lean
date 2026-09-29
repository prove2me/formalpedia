-- Prove2me | Theorems.Thm_lean_workbook_plus_25742
-- name    : lean_workbook_plus_25742
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d6955566-1aba-47dd-a73f-e225202dc6eb
-- statement:
--   $ \sum_{d=1}^{e}\frac{1}{6}d (d+1) (d+2)=\frac{1}{24}e (e+1) (e+2) (e+3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25742 : ∀ e : ℕ, ∑ d in Finset.Icc 1 e, (1/6 * d * (d+1) * (d+2)) = (1/24 * e * (e+1) * (e+2) * (e+3))   :=  by sorry
