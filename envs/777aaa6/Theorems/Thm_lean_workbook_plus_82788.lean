-- Prove2me | Theorems.Thm_lean_workbook_plus_82788
-- name    : lean_workbook_plus_82788
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/81a0f00c-468c-4a7c-af73-a5c2bab9c51a
-- statement:
--   Find the general term formula for the sequence: $a_0=2$, $a_{n+1}+3a_n=n^3-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82788 (a : ℕ → ℤ) (a0 : a 0 = 2) (a_rec : ∀ n, a (n + 1) + 3 * a n = n ^ 3 - 1) : ∃ f : ℕ → ℤ, ∀ n, a n = f n   :=  by sorry
