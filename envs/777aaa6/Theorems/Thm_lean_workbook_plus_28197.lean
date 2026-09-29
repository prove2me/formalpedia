-- Prove2me | Theorems.Thm_lean_workbook_plus_28197
-- name    : lean_workbook_plus_28197
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/677e1470-3a9e-4fc6-a8e1-755f0e038d8c
-- statement:
--   Define the sequence $\{a_n\}_{n=1}^{\infty}$, where\n\n$a_n = 9n^2 \cdot \pi(n) + 1$.\n\nObserve that\n\n$a_4 = 9 \cdot 4^2 \cdot \pi (4) + 1 = 9 \cdot 16 \cdot 2 + 1 = 16 \cdot 18 + 1 = (17 - 1)(17 + 1) + 1 = 17^2$\n\nand\n\n$a_5 = 9 \cdot 5^2 \cdot \pi (5) + 1 = 9 \cdot 25 \cdot 3 + 1 = 25 \cdot 27 + 1 = (26 - 1)(26 + 1) + 1 = 26^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28197  (a : ℕ → ℕ)
  (h₀ : ∀ n, a (n + 2) = (9 * (n + 2)^2 * Nat.totient (n + 2) + 1)) :
  a 4 = 17^2 ∧ a 5 = 26^2   :=  by sorry
