-- Prove2me | Theorems.Thm_lean_workbook_plus_23349
-- name    : lean_workbook_plus_23349
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e9f9b9e1-d9db-4720-a739-48e13b1467ae
-- statement:
--   Show that x and y are consecutive numbers $x=\prod_{i=1}^{n}(a_{i}+1),y=2\prod_{i=2}^{n} a_{i}$ , where $(a_{n})_{n\geq 1},a_{1}=\sqrt{2},a_{2}=2,a_{n+1}=a_{n}a_{n-1}^{2},n\geq 2$ ,n natural number greater than 2 or egual to 2
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23349 (n : ℕ) (a : ℕ → ℕ) (a1 : a 0 = Real.sqrt 2) (a2 : a 1 = 2) (a_rec : ∀ n, a (n + 1) = a n * (a (n - 1))^2) : ∃ x y, x = ∏ i in Finset.range (n + 1), (a i + 1) ∧ y = 2 * ∏ i in Finset.range (n + 1), a i   :=  by sorry
