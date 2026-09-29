-- Prove2me | Theorems.Thm_lean_workbook_plus_80412
-- name    : lean_workbook_plus_80412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/136f3d2a-060e-48cc-9049-66b4757703dd
-- statement:
--   Find the closed form of the sequence $(a_n)$ defined as $a_1 = 33$, $a_2 = 49$, $a_3 = 177$, and $a_{n+3} = 8a_{n+2} - 8a_{n+1} + a_n$ for all $n \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80412 (a : ℕ → ℤ) (a1 : a 0 = 33) (a2 : a 1 = 49) (a3 : a 2 = 177) (a_rec : ∀ n, n ≥ 1 → a (n + 3) = 8 * a (n + 2) - 8 * a (n + 1) + a n) : ∃ f : ℕ → ℤ, ∀ n, n ≥ 1 → a n = f n   :=  by sorry
