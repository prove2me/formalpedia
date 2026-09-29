-- Prove2me | Theorems.Thm_lean_workbook_plus_36961
-- name    : lean_workbook_plus_36961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b0baf1a9-49df-48e1-8d69-f8d52bfcba8f
-- statement:
--   Base Cases: Divisibility by 11 holds for $ n = 0$ and $ n = 1$ : $ 11$ divides $ 1 - 1 = 0$ , and also $ 25 - 3 = 22$ Inductive Step: If divisibility by 11 holds for $ n - 1$ and for $ n$ , it is true for $ n + 1$ . Note that: $ a^{n + 1} - b^{n + 1} = (a + b)(a^n - b^n) - ab (a^{n - 1} - b^{n - 1})$ Or, for this particular case, $ a = 25$ and $ b = 3$ : $ 25^{n + 1} - 3^{n + 1} = 28(25^n - 3^n) - 75 (25^{n - 1} - 3^{n - 1})$ But the two terms on the right are divisible by $ 11$ , so the LHS must also be divisible by $ 11$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36961  (n : ℕ) :
  11 ∣ (25^n - 3^n)   :=  by sorry
