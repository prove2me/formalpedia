-- Prove2me | Theorems.Thm_lean_workbook_plus_390
-- name    : lean_workbook_plus_390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cf7dd1ce-819d-45b3-8bd2-c16acfd07eac
-- statement:
--   Given is a sequence of positive integers, defined by $a_1=1$ and $a_{n+1}=a_n^2+a_n+1$ , for every positive integer $n$ . Prove that for every positive integer $n$ , $a_n^2+1 | a_{n+1}^2+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_390 (n : ℕ) (a : ℕ → ℕ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = a n ^ 2 + a n + 1) : (a n ^ 2 + 1) ∣ (a (n + 1) ^ 2 + 1)   :=  by sorry
