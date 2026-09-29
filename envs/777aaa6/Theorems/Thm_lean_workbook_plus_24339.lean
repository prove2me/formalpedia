-- Prove2me | Theorems.Thm_lean_workbook_plus_24339
-- name    : lean_workbook_plus_24339
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8c1c39f8-accc-41d3-bda9-7fdb4c964158
-- statement:
--   Prove that $\big(\frac{1}{2}\big)^2\big(\frac{3}{4}\big)^2\cdots \big(\frac{2n-1}{2n}\big)^2 < \frac{1}{3n}, \forall \ n\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24339 : ∀ n : ℕ, (∏ i in Finset.range n, ((2 * i - 1) / (2 * i))) ^ 2 < 1 / (3 * n)   :=  by sorry
