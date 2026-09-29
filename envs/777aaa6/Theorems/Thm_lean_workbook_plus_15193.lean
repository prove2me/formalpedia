-- Prove2me | Theorems.Thm_lean_workbook_plus_15193
-- name    : lean_workbook_plus_15193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/baacad97-c3c4-4f97-b85f-a8c185e9df70
-- statement:
--   Find a function $f : \mathbb{R} \rightarrow \mathbb{R}$ that satisfies $f(x) = x^3$ and check if it fits the original equation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15193 (f : ℝ → ℝ) (hf: f = fun x => x^3) : ∀ x, f x = x^3   :=  by sorry
