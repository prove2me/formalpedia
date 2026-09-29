-- Prove2me | Theorems.Thm_lean_workbook_plus_10522
-- name    : lean_workbook_plus_10522
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2cd6a2e0-0984-4f95-bc85-4dd32e5a3198
-- statement:
--   Prove that \( f(f(x))=x \) for the function \( f(x)=x \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10522 (f : ℝ → ℝ) (x : ℝ) (h₁ : f x = x) : f (f x) = x   :=  by sorry
