-- Prove2me | Theorems.Thm_lean_workbook_plus_71131
-- name    : lean_workbook_plus_71131
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fd679191-3fc5-4972-9688-1241939ebde2
-- statement:
--   Solve the recurrence relation $p(n, k) = \frac{3 - k}{3}p(n - 1, k - 1) + \frac{k}{3}p(n - 1, k + 1)$ for $p(n, k)$, given $p(1, 0) = 1$ and $p(n, 0) = p(n, 1) = 0$ for $n > 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71131 (p : ℕ → ℕ → ℚ) (hp : p 1 0 = 1) (hp2 : ∀ n, 1 < n → p n 0 = 0 ∧ p n 1 = 0) (hp3 : ∀ n k, 1 < n ∧ 1 < k → p n k = (3 - k) / 3 * p (n - 1) (k - 1) + k / 3 * p (n - 1) (k + 1)) : ∀ n k, p n k = (n! * 3^(n - 1))⁻¹   :=  by sorry
