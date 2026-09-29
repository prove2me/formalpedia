-- Prove2me | Theorems.Thm_lean_workbook_plus_9753
-- name    : lean_workbook_plus_9753
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/9179d879-187f-4fb4-8ab6-4906fccb1ba1
-- statement:
--   Find the closed formula of the following recurrence relation: \n\n $ a_0 = 6$ \n $ a_{n+1} = (2n+2)a_{n} - 15n-10$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9753 (a : ℕ → ℕ) (a0 : a 0 = 6) (a_rec : ∀ n, a (n+1) = (2*n+2)*a n - 15*n - 10) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
