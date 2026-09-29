-- Prove2me | Theorems.Thm_lean_workbook_plus_14505
-- name    : lean_workbook_plus_14505
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9ce8b45f-df3b-429b-a2ec-c645c68de081
-- statement:
--   Find the closed form expression for $a_n$ in the sequence $(a_n)$ defined by $a_{1}=0, a_{2}=3$ and $a_{n+2}=7a_{n+1}-a_{n}+3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14505 (a : ℕ → ℤ) (a1 : a 0 = 0) (a2 : a 1 = 3) (a_rec : ∀ n, a (n + 2) = 7 * a (n + 1) - a n + 3) : ∃ f : ℕ → ℤ, ∀ n, a n = f n   :=  by sorry
