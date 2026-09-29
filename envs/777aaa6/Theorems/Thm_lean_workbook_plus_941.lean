-- Prove2me | Theorems.Thm_lean_workbook_plus_941
-- name    : lean_workbook_plus_941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/656d275d-2b18-4f9d-af17-e41f0efa109e
-- statement:
--   Prove that $f(n)=2-n$ for all $n\in \mathbb{Z}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_941 (f : ℤ → ℤ) (hf: f = fun n => 2 - n) : ∀ n, f n = 2 - n   :=  by sorry
