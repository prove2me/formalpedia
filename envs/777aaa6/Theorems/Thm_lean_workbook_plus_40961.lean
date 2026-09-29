-- Prove2me | Theorems.Thm_lean_workbook_plus_40961
-- name    : lean_workbook_plus_40961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a16510c0-4b5a-4f97-95b5-f2582c8742a6
-- statement:
--   Find an explicit formula for the sequence defined by $a_0=5$, $a_1=35$, and $a_{n+2}=8a_{n+1}-a_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40961 (a : ℕ → ℤ) (a0 : a 0 = 5) (a1 : a 1 = 35) (a_rec : ∀ n, a (n + 2) = 8 * a (n + 1) - a n) : ∃ f : ℕ → ℤ, ∀ n, a n = f n   :=  by sorry
