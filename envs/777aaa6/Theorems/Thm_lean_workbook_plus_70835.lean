-- Prove2me | Theorems.Thm_lean_workbook_plus_70835
-- name    : lean_workbook_plus_70835
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/87526ff1-5edf-4059-b486-0bca26c58499
-- statement:
--   Each term is $2^{n+1}-1$ , where $n$ is the layer. Adding all of these is equivalent to finding $2^2+2^3+2^4...+2^{21}-20$ . By the geometric series formula, $2^2+2^3+2^4...+2^{21}-20=4194300-20=4194280$ . From here, we can test to find that the answer is $n=\boxed{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70835  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∑ k in Finset.Icc 1 n, (2^(k + 1) - 1) = 4194280) :
  n = 3   :=  by sorry
