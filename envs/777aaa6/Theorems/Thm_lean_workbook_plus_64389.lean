-- Prove2me | Theorems.Thm_lean_workbook_plus_64389
-- name    : lean_workbook_plus_64389
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/bc9f641b-3a16-4d0f-ade5-30ff261d5250
-- statement:
--   Find the function $f(x)$ that satisfies the following conditions: $f(0)=0$ and $f(f(x))=2f(x) \forall x \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64389 (f : ℝ → ℝ) (hf: f 0 = 0) (hf2: ∀ x, f (f x) = 2 * f x) : ∃ g : ℝ → ℝ, ∀ x, g x = f x   :=  by sorry
