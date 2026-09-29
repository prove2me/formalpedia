-- Prove2me | Theorems.Thm_lean_workbook_plus_17017
-- name    : lean_workbook_plus_17017
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d9047dcc-c7a7-401a-bc95-ef753f435bb1
-- statement:
--   Find a formula $ a_n$ in term of $ n$ for the sequence $ \{a_n\}$ defined by $ a_0=1$ and $ a_{n+1}=5a_n\left(5a_n^4-5a_n^2+1\right)$ for all $ n\geq0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17017 (a : ℕ → ℕ) (a0 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = 5 * a n * (5 * a n ^ 4 - 5 * a n ^ 2 + 1)) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
