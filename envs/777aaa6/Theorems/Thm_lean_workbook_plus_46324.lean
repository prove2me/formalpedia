-- Prove2me | Theorems.Thm_lean_workbook_plus_46324
-- name    : lean_workbook_plus_46324
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d12e5677-fbf9-4f6a-81bd-0dbb4cd5f7db
-- statement:
--   Let $n$ be the number of numbers in the list and $s$ be their sum. Because Lara multiplied each number in the list by $3$ , the sum of the numbers in the list also increased by a factor of $3$ . It follows that $s = 15$ . Additionally, because Maddy added $3$ to each number in the list, the overall sum became $s + 3n = 15 + 3n$ . Setting this equal to $45$ and solving yields $n = 10$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46324  (n s : ℕ)
  (h₀ : 0 < n)
  (h₁ : s = 15)
  (h₂ : s + 3 * n = 45) :
  n = 10   :=  by sorry
