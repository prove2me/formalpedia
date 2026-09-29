-- Prove2me | Theorems.Thm_lean_workbook_plus_15515
-- name    : lean_workbook_plus_15515
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/40f10693-bc25-43d0-9f37-2011caa19b0c
-- statement:
--   $ a_{n + 1}^2 - 3a_na_{n + 1} + 2a_{n}^2 = (a_{n + 1} - a_n)(a_{n + 1} - 2a_{n}) = 0$ , so $ a_{n + 1} = a_n\ \text{or}\ 2a_n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15515  (a : ℕ → ℝ)
  (n : ℕ)
  (h₀ : (a (n + 1))^2 - 3 * a n * a (n + 1) + 2 * (a n)^2 = 0) :
  a (n + 1) = a n ∨ a (n + 1) = 2 * a n   :=  by sorry
