-- Prove2me | Theorems.Thm_lean_workbook_plus_72464
-- name    : lean_workbook_plus_72464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/dbb51e19-2e9b-45bd-ac75-f7f82a5d1e28
-- statement:
--   Let $M=\sum \frac{a_i}{a_{i+1}+a_{i+2}}$, $N=\sum \frac{a_{i+1}}{a_{i+1}+a_{i+2}}$, $T= \sum \frac{a_{i+2}}{a_{i+1}+a_{i+2}}$. Clearly, $N+T=n$. Also, with AM-GM, $M+N\geq n$ and $M+T\geq n$. Therefore, summing up these two inequalities: $2M+(N+T)\geq 2n$. Hence $M\geq \frac{n}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72464  (a : ℕ → ℝ)
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, a i > 0)
  (h₂ : ∀ i, a (i + 1) + a (i + 2) ≠ 0)
  (h₃ : n = (Finset.range n).sum (fun i => a i / (a (i + 1) + a (i + 2)))) :
  n / 2 ≤ (Finset.range n).sum (fun i => a i / (a (i + 1) + a (i + 2)))   :=  by sorry
