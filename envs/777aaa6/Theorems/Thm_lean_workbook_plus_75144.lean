-- Prove2me | Theorems.Thm_lean_workbook_plus_75144
-- name    : lean_workbook_plus_75144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2e194286-10a3-4b08-b763-80abb98571b4
-- statement:
--   The least 3-digit integer that is divisible by 7 is $105=7\cdot15$ . The greatest is $994=7\cdot 142$ . The 3-digit integers that are divisible by $7$ are the $15^\text{th}$ multiple to the $142^\text{nd}$ multiple inclusive. This is $142-15+1=128$ 3-digit numbers that are divisible by $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75144  (n : ℕ)
  (h₀ : 7 * 15 ≤ n)
  (h₁ : n ≤ 7 * 142) :
  Finset.card (Finset.filter (λ x => 7∣x) (Finset.Icc 100 999)) = 128   :=  by sorry
