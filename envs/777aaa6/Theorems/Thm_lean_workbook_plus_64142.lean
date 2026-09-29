-- Prove2me | Theorems.Thm_lean_workbook_plus_64142
-- name    : lean_workbook_plus_64142
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ad01e4d0-c57c-4b44-b292-79aae37b4a93
-- statement:
--   Let $d$ be a positive integer. Show that for every integer $S$ , there exists an integer $n>0$ and a sequence of $n$ integers $\epsilon_1, \epsilon_2,..., \epsilon_n$ , where $\epsilon_i = \pm 1$ (not necessarily dependent on each other) for all integers $1\le i\le n$ , such that $S=\sum_{i=1}^{n}{\epsilon_i(1+id)^2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64142 (d S : ℤ) (hd : d > 0) : ∃ n : ℕ, ∃ ε : Fin n → ℤ, ∑ i, ε i * (1 + i * d) ^ 2 = S   :=  by sorry
