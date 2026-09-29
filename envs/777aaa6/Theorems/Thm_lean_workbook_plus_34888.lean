-- Prove2me | Theorems.Thm_lean_workbook_plus_34888
-- name    : lean_workbook_plus_34888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/48d51f8e-3d1c-41ec-925c-35296d2c5322
-- statement:
--   Find the closed form of the sequence $(a_n)$ defined as $a_0=1,a_1=2$ and $a_{n+2}=4a_{n+1}+a_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34888 (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 2) (a_rec : ∀ n, a (n + 2) = 4 * a (n + 1) + a n) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
