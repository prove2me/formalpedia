-- Prove2me | Theorems.Thm_lean_workbook_plus_71314
-- name    : lean_workbook_plus_71314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/0339ef3c-7166-4720-8946-e672b5d1a454
-- statement:
--   Train A passes a milestone in 8 seconds before meeting train B. The two trains pass each other in 9 seconds. Then train B passes the same milestone in 12 seconds.\n\nWhich of the following statements about the lengths of the trains is true?\n\na, A is twice as long as B\nb, A and B are of equal length\nc, B is 50% longer than A\nd, B is twice as long as A\ne, cannot be deducted about the length of A and B\n\nAssume that Train A's length to be $x$ and it's speed $a$ , and Train B's, $y$ and $b$ , respectively.\n\nFrom the question, we know that\n\n$x=8a$ (i)\n\n$y=12b$\n\n$\frac{x+y}{a+b}= 9$\n\n\nThen, we have $x+y=9a+9b \to 8a+12b=9a+9b \to 3b=a$\n\nSubstituing the latter into (i), we get $x=24b=2y$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71314  (x y a b : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < a ∧ 0 < b)
  (h₁ : x = 8 * a)
  (h₂ : y = 12 * b)
  (h₃ : (x + y) / (a + b) = 9) :
  x = 2 * y   :=  by sorry
