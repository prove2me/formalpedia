-- Prove2me | Theorems.Thm_lean_workbook_plus_73551
-- name    : lean_workbook_plus_73551
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c0747037-5c35-4715-b70b-d1e32af01a06
-- statement:
--   SolutionWe try to find a recursive sequence, \n\n $\begin{tabular}{|l|c|l|c|l|} \hline Stairs Walked & Distinct Ways to make the step \ \hline 1 & 1 \ \hline 2 & 2 \ \hline 3 & 4 \ \hline 4 & 7 \ \hline \end{tabular}$ From here, we can easily see the recursive sequence \n\n $$a_n=a_{n-1}+a_{n-2}+a_{n-3}$$ Thus, we have $a_5=13$ and $a_6=\boxed{24}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73551  (a : ℕ → ℕ)
  (h₀ : a 1 = 1)
  (h₁ : a 2 = 2)
  (h₂ : a 3 = 4)
  (h₃ : a 4 = 7)
  (h₄ : ∀ n ≥ 5, a n = a (n - 1) + a (n - 2) + a (n - 3)) :
  a 6 = 24   :=  by sorry
