-- Prove2me | Theorems.Thm_lean_workbook_plus_64318
-- name    : lean_workbook_plus_64318
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/73843658-f555-4231-906a-ad57216ad466
-- statement:
--   Setting $A=\sum\limits_{i=1}^{n}{t(k)}$ , $B=\sum\limits_{i=1}^{n}{s(k)}$ . We have $ A+B=n(2n+1), A-B=\frac{n(n+3)}{2} $ This implies that $B+n=\frac{3n(n+1)}{4}$ . Since $B$ is an integer, it is obvious that $4|n(n+1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64318  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∃ (A B : ℕ), A + B = n * (2 * n + 1) ∧ A - B = n * (n + 3) / 2) :
  4 ∣ n * (n + 1)   :=  by sorry
