-- Prove2me | Theorems.Thm_lean_workbook_plus_71094
-- name    : lean_workbook_plus_71094
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/eb3a2513-ff7e-465d-b9a4-69014178bd1b
-- statement:
--   Update : \n $\begin{array}{l}a_2^2 = {a_1}{a_3}{\rm{ }}\\a_3^2 = {a_2}{a_4}{\rm{ }}\\a_4^2 = {a_3}{a_5}\\a_5^2 = {a_4}{a_1}\\\sum\limits_{i = 1}^5 {{a_i}} = 2010\end{array}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71094 : ∃ a : ℕ → ℕ, a 2^2 = a 1 * a 3 ∧ a 3^2 = a 2 * a 4 ∧ a 4^2 = a 3 * a 5 ∧ a 5^2 = a 4 * a 1 ∧ ∑ i in Finset.range 5, a i = 2010   :=  by sorry
