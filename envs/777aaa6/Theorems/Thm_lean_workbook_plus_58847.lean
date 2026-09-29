-- Prove2me | Theorems.Thm_lean_workbook_plus_58847
-- name    : lean_workbook_plus_58847
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/78869d66-972f-46e7-94b2-e3a2c6f66da6
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ such that $f(x) + f(y) \leqslant 2 - \left| x-y \right|$ for all $x,y \in \mathbb R$ . Prove that $f(x) \leq 1$ , for all $x \in \mathbb R$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58847 (f : ℝ → ℝ) (h : ∀ x y : ℝ, f x + f y ≤ 2 - abs (x - y)) : ∀ x : ℝ, f x ≤ 1   :=  by sorry
