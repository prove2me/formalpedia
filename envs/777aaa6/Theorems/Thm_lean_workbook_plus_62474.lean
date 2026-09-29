-- Prove2me | Theorems.Thm_lean_workbook_plus_62474
-- name    : lean_workbook_plus_62474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2226dca7-cc80-47a6-b712-397689d92bdc
-- statement:
--   Computing the first few terms of the sequence, you will get $x_{0}=1, x_{1}=2, x_{2}=3, x_{3}=2, x_{4}=1$. Again, $x_{5}=1,x_{6}=2,x_{7}=3,x_{8}=2,x_{9}=1$ and so on. So, the sequence $1,2,3,2,1$ keeps on repeating itself. As $2014=5k-1$, so $x_{2014}=x_{4}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62474  (x : ℕ → ℕ)
  (h₀ : x 0 = 1)
  (h₁ : x 1 = 2)
  (h₂ : x 2 = 3)
  (h₃ : x 3 = 2)
  (h₄ : x 4 = 1)
  (h₅ : ∀ n, x (n + 5) = x n) :
  x 2014 = 1   :=  by sorry
