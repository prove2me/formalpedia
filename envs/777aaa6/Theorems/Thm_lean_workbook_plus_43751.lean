-- Prove2me | Theorems.Thm_lean_workbook_plus_43751
-- name    : lean_workbook_plus_43751
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7c4ac7ff-b7cc-469f-b03f-de5fc0c851d1
-- statement:
--   Prove that for any integer $n\ge2$ , there exist positive integer $a_1,a_2,...,a_n$ such that $a_j-a_i$ divides $a_j+a_i$ for $1\le i<j\le n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43751 (n : ℕ) (_hn : 2 ≤ n) :
    ∃ a : ℕ → ℕ,
      ∀ i j : ℕ,
        i < j →
          i ≤ n ∧
            j ≤ n →
              (a j - a i) ∣ (a j + a i)   :=  by sorry
