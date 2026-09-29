-- Prove2me | Theorems.Thm_lean_workbook_plus_50065
-- name    : lean_workbook_plus_50065
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/23223b17-6ec7-49a9-9169-62b9291d6fee
-- statement:
--   $\boxed{\text{S3 : }f(x)=x^2\quad\forall x\in\mathbb Z}$ , which indeed fits
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50065 (f : ℤ → ℤ) (hf: f = fun x ↦ x^2) : ∀ x, f x = x^2   :=  by sorry
