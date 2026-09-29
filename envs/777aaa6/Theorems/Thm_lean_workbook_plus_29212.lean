-- Prove2me | Theorems.Thm_lean_workbook_plus_29212
-- name    : lean_workbook_plus_29212
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b81cfeff-92d1-439c-a630-aef5a2a69cd5
-- statement:
--   For all positive integers $ n$ , let $ f(n) = \log_{2002} n^2$ . Let $ N = f(11) + f(13) + f(14) $ Which of the following relations is true? \n\n $ \textbf{(A)}\ N < 1 \qquad \textbf{(B)}\ N = 1 \qquad \textbf{(C)}\ 1 < N < 2 \qquad \textbf{(D)}\ N = 2 \qquad \textbf{(E)}\ N > 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29212  (n : ℕ)
  (f : ℕ → NNReal)
  (N : ℝ)
  (h₀ : 0 < n)
  (h₁ : ∀ n, f n = Real.logb 2002 (n ^ 2))
  (h₂ : N = f 11 + f 13 + f 14) :
  N = 2   :=  by sorry
