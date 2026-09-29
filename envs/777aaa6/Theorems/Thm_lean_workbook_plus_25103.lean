-- Prove2me | Theorems.Thm_lean_workbook_plus_25103
-- name    : lean_workbook_plus_25103
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/465562ca-8529-4faa-9cee-13651e6d29be
-- statement:
--   Let $ x_{1},x_{2},...,x_{n}\geq 0,x_{1}^{4}+x_{2}^{4}+...+x_{n}^{4}= 1$ , prove that: $ \sqrt [3]{x_{1}+x_{2}+...+x_{n}}\geq\sqrt{x_{1}^{2}+x_{2}^{2}+...+x_{n}^{2}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25103 (n : ℕ) (x : ℕ → NNReal) (hx : ∑ i in Finset.range n, (x i)^4 = 1) : (∑ i in Finset.range n, x i)^(1/3) ≥ (∑ i in Finset.range n, (x i)^2)^(1/2)   :=  by sorry
