-- Prove2me | Theorems.Thm_lean_workbook_plus_56268
-- name    : lean_workbook_plus_56268
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/998a4be9-5b15-472b-ac84-9506fa6c109f
-- statement:
--   Let $N$ be a three digit number, i.e. $N = \overline{abc}$ . Permutating the three digit of $N$ , we obtain six three digit numbers (including $N$ ) which sum is $\overline{abc} + \overline{acb} + \overline{bac} + \overline{bca} + \overline{cab} + \overline{cba} = 2(100 + 10 + 1)(a + b + c) = 222(a + b + c) = 222T$ , where $T$ is the sum of digits of $N$ . Hence the sum $S(N)$ of the five numbers (excluding $N$ ) which are digital permutations of $N$ are $(1) \;\; S(N) = 222T - N$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56268  (a b c : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9)
  (h₁ : 1 ≤ b ∧ b ≤ 9)
  (h₂ : 1 ≤ c ∧ c ≤ 9)
  (N : ℕ)
  (h₃ : N = 100 * a + 10 * b + c)
  (h₄ : 0 < N) :
  N + (100 * a + 10 * c + b) + (100 * b + 10 * a + c) + (100 * b + 10 * c + a) + (100 * c + 10 * b + a) + (100 * c + 10 * a + b) = 222 * (a + b + c)   :=  by sorry
