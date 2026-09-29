-- Prove2me | Theorems.Thm_lean_workbook_plus_41853
-- name    : lean_workbook_plus_41853
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b51a40d6-67fe-4e91-9db0-93ac68f79d80
-- statement:
--   prove that $\frac{\sqrt{6}}{5}+\frac{\sqrt{20}}{9}+\frac{\sqrt{42}}{13}+..............+\frac{\sqrt{2n(n+1)}}{4n+1}<\frac{n}{2}$ for all $n\in {N^{*}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41853 : ∀ n : ℕ, (∑ k in Finset.range n, (Real.sqrt (2 * k * (k + 1)) / (4 * k + 1))) < n / 2   :=  by sorry
