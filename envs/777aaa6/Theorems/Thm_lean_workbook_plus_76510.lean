-- Prove2me | Theorems.Thm_lean_workbook_plus_76510
-- name    : lean_workbook_plus_76510
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1fa4218a-3442-441f-b89b-db2725686bc7
-- statement:
--   For all positive integers $n$ , let $f(n)=\log_{2002} n^2$ . Let $N=f(11)+f(13)+f(14)$ . Which of the following relations is true?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76510  (n : ℕ)
  (f : ℕ → NNReal)
  (N : ℝ)
  (h₀ : 0 < n)
  (h₁ : ∀ n, f n = Real.logb 2002 (n ^ 2))
  (h₂ : N = f 11 + f 13 + f 14) :
  Real.logb 2002 (11 ^ 2) = Real.logb 2002 (13 ^ 2) + Real.logb 2002 (14 ^ 2)   :=  by sorry
