-- Prove2me | Theorems.Thm_lean_workbook_plus_59764
-- name    : lean_workbook_plus_59764
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b145e75e-7d27-4348-9111-d87ca3d21c86
-- statement:
--   And so $f(f(x))=2x-f(x)$ $\forall x\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59764 (f : ℝ → ℝ) (hf: f (f x) = 2 * x - f x) (hx: x ≥ 0) : f (f x) = 2 * x - f x   :=  by sorry
