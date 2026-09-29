-- Prove2me | Theorems.Thm_lean_workbook_plus_5909
-- name    : lean_workbook_plus_5909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b7cf708d-a426-427e-82f7-f3d8446e1c30
-- statement:
--   For all integers $1 \leq k \leq n$ let $S_k = {a_{5k-4}}^2 + a_{5k-3}^2 + a_{5k-2}^2 + a_{5k-1}^2 + a_{5k}^2$. Show that $S_k \geq a_{5k-4}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5909 (n : ℕ) (a : ℕ → ℤ) (k : ℕ) (h₁ : 1 ≤ k ∧ k ≤ n) : (a (5 * k - 4))^2 + (a (5 * k - 3))^2 + (a (5 * k - 2))^2 + (a (5 * k - 1))^2 + (a (5 * k))^2 ≥ a (5 * k - 4)   :=  by sorry
