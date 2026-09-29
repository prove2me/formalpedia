-- Prove2me | Theorems.Thm_lean_workbook_plus_40086
-- name    : lean_workbook_plus_40086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/35adabd2-8713-49b5-a45d-4df70dae4cbb
-- statement:
--   Let $P(x,y)$ be the assertion $f(f(x)+xf(y))=xy+f(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40086 (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (f x + x * f y) = x * y + f x   :=  by sorry
