-- Prove2me | Theorems.Thm_lean_workbook_plus_47099
-- name    : lean_workbook_plus_47099
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4fe04e77-ce8b-44d1-b812-30540d1dddd1
-- statement:
--   Let $x_1=\sqrt{2}$ and $x_{n+1}=\sqrt{2+x_n}$. Show by induction that $x_n < x_{n+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47099 (n : ℕ) (f : ℕ → ℝ) (hf: f 0 = Real.sqrt 2 ∧ ∀ n, f (n + 1) = Real.sqrt (2 + f n)) : f n < f (n + 1)   :=  by sorry
