-- Prove2me | Theorems.Thm_lean_workbook_plus_4698
-- name    : lean_workbook_plus_4698
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b907bdfe-eb18-46c8-8d59-0f35eb320559
-- statement:
--   Let $a$ be the number of students that do neither choir nor basketball, $b$ the number of students that do basketball but not choir, $c$ the number of students that do choir but not basketball, and $d$ the number that do both. Then we are given: $a = 14$, $d = 11$, $b+d = 18 \Rightarrow b = 7$, $c+d = 15 \Rightarrow c = 4$. Thus the total number of students is $a+b+c+d = 11+7+4+14 = 36$. Your solution book is wrong.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4698  (a b c d : ℕ)
  (h₀ : a = 14)
  (h₁ : b + d = 18)
  (h₂ : c + d = 15)
  (h₃ : d = 11) :
  a + b + c + d = 36   :=  by sorry
