-- Prove2me | Theorems.Thm_lean_workbook_plus_31794
-- name    : lean_workbook_plus_31794
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d239ba1a-2a2a-4c01-9dc8-4f3de4bc1211
-- statement:
--   Given a function $f:A\to B$, how can we determine if it is injective?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31794 (f : A → B) : Function.Injective f ↔ ∀ x y, x ≠ y → f x ≠ f y   :=  by sorry
