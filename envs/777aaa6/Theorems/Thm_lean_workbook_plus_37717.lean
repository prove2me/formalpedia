-- Prove2me | Theorems.Thm_lean_workbook_plus_37717
-- name    : lean_workbook_plus_37717
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a979dc50-30ba-48b3-b2ed-43b5c5cb05bc
-- statement:
--   Let's find the sum of three three-digit numbers where each digit from 1 to 9 is used exactly once. Express the numbers as $100a + 10b + c$, $100a_1 + 10b_1 + c_1$, and $100a_2 + 10b_2 + c_2$. Show that the sum is a multiple of 9 and find a value that is not a possible sum.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37717 (a b c a1 b1 c1 a2 b2 c2 : ℕ) (hab : a ≠ a1) (hbc : b ≠ b1) (hca : c ≠ c1) (hab1 : a1 ≠ a2) (hbc1 : b1 ≠ b2) (hca1 : c1 ≠ c2) (hA: a + a1 + a2 = 9) (hB: b + b1 + b2 = 9) (hC: c + c1 + c2 = 9) : 9 ∣ (100 * a + 10 * b + c) + (100 * a1 + 10 * b1 + c1) + (100 * a2 + 10 * b2 + c2)   :=  by sorry
