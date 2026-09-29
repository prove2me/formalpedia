-- Prove2me | Theorems.Thm_lean_workbook_plus_47093
-- name    : lean_workbook_plus_47093
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/be1d085b-5149-484b-bbe0-8dfa2c1ae58f
-- statement:
--   Given $a \in R$ and any sequence of positive numbers $c_n$, prove that there are positive integers $y_n$ such that $\sum c_n|\sin(ny_na)| < \infty$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47093 (a : ℝ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) :
    ∃ y : ℕ → ℕ, Summable fun n : ℕ => c n * |Real.sin (n * y n * a)|   :=  by sorry
