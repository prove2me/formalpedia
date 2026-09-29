-- Prove2me | Theorems.Thm_lean_workbook_plus_5022
-- name    : lean_workbook_plus_5022
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/60027801-5001-41d7-98ba-39cb09895554
-- statement:
--   \begin{tabular}[t]{c|c|c|c|c|c|c|c|c|} 0 & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 \\hline 1 & 127 & 51 & 21 & 9 & 4 & 2 & 1 & 1 \\hline 2 & 196 & 76 & 30 & 12 & 5 & 2 & 1 & 0 \\hline 3 & 189 & 69 & 25 & 9 & 3 & 1 & 0 & 0 \\hline 4 & 133 & 44 & 14 & 4 & 1 & 0 & 0 & 0 \\hline 5 & 70 & 20 & 5 & 1 & 0 & 0 & 0 & 0 \\hline 6 & 27 & 6 & 1 & 0 & 0 & 0 & 0 & 0 \\hline 7 & 7 & 1 & 0 & 0 & 0 & 0 & 0 & 0 \\hline 8 & 1 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\hline \end{tabular} We seek to count the number of sequences we can construct of length $7$ (and thus $0$ elements left to add), and so we sum the column $x = 0$ to obtain $\boxed{750}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5022  (a : ℕ → ℕ)
  (h₀ : a 0 = 1)
  (h₁ : a 1 = 127)
  (h₂ : a 2 = 196)
  (h₃ : a 3 = 189)
  (h₄ : a 4 = 133)
  (h₅ : a 5 = 70)
  (h₆ : a 6 = 27)
  (h₇ : a 7 = 7)
  (h₈ : a 8 = 1) :
  ∑ k in Finset.range 9, a k = 750   :=  by sorry
