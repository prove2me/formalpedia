-- Prove2me | Theorems.Thm_WorkbookSource_problem_21770
-- name    : WorkbookSource.problem_21770
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:28.946611+00:00
-- url     : https://prove2.me/theorems/e3a2fc61-6da5-403f-ae31-3073e12d847a
-- title:
--   Eliminating an auxiliary recurrence
-- statement:
--   We have ${{b}_{n+1}}=5{{a}_{n+2}}-2{{a}_{n+1}}$ and also ${{b}_{n}}=5{{a}_{n+1}}-2{{a}_{n}}$ , replace in ${{b}_{n+1}}=\frac{3}{5}{{b}_{n}}+\frac{2}{5}{{a}_{n+1}}$ we have: $$5{{a}_{n+2}}-2{{a}_{n+1}}=\frac{3}{5}(5{{a}_{n+1}}-2{{a}_{n}})+\frac{2}{5}{{a}_{n+1}}$$ $$\Rightarrow 5a_{n+2} -\frac{27}{5}a_{n+1} +\frac{6}{5}a_{n} =0$$ Characteristic equation: $5\lambda ^2-\frac{27}{5}\lambda +\frac{6}{5}=0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21770` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21770; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_21770 (n : ℕ) (a : ℕ → ℝ) (b : ℕ → ℝ) (h₀ : 5 * a (n + 2) - 2 * a (n + 1) = b (n + 1))  (h₁ : 5 * a (n + 1) - 2 * a n = b n) (h₂ : b (n + 1) = 3 / 5 * b n + 2 / 5 * a (n + 1)) : 5 * a (n + 2) - 27 / 5 * a (n + 1) + 6 / 5 * a n = 0  :=  by sorry
