-- Prove2me | Theorems.Thm_lean_workbook_plus_46905
-- name    : lean_workbook_plus_46905
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b8497399-f97b-4af2-a4f0-a1957b7cf221
-- statement:
--   Let A be an $n\times m$ matrix, and $b\in \mathbb R^n$ . Suppose $Ax = b$ has at least one solution $x_0\in \mathbb R^m$ Show all solutions are of the form $x = x_0 + h$ , where $h$ solves $Ah = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46905 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (x0 : Fin m → ℝ) (h : A.mulVec x0 = b) : ∀ x : Fin m → ℝ, A.mulVec x = b ↔ ∃ h : Fin m → ℝ, x = x0 + h ∧ A.mulVec h = 0   :=  by sorry
