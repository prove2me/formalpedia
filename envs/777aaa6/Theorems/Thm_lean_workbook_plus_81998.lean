-- Prove2me | Theorems.Thm_lean_workbook_plus_81998
-- name    : lean_workbook_plus_81998
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7022946f-25d6-482b-a977-7de7cb612dc6
-- statement:
--   Prove that for every integer $n > 1$ the equation $\sum^n_{k=0} \frac{x^k}{k!} = 0$ has no rational roots.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81998 : ∀ n : ℕ, 1 < n → ¬∃ x : ℚ, ∑ k in Finset.range n, (x : ℂ)^k / k! = 0   :=  by sorry
