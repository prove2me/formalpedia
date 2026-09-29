-- Prove2me | Theorems.Thm_lean_workbook_plus_49838
-- name    : lean_workbook_plus_49838
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5609d425-604b-4358-b70b-63e3540e2aba
-- statement:
--   Prove that $\sum a_i = \sum b_i$ is a necessary condition for the inequality $\sum_{sym} x^{a_1}y^{a_2} + \cdots + \sum_{sym} x^{a_{2n-1}}y^{a_{2n}} \ge \sum_{sym} x^{b_1}y^{b_2} + \cdots + \sum_{sym} x^{b_{2n-1}}y^{b_{2n}}$ to hold for all $x,y \in \mathbb{R}^+$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49838 (n : ℕ) (a b : ℕ → ℕ) (hab : a = b) : ∑ i in Finset.range (2 * n), a i = ∑ i in Finset.range (2 * n), b i   :=  by sorry
