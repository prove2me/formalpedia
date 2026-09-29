-- Prove2me | Theorems.Thm_lean_workbook_plus_48772
-- name    : lean_workbook_plus_48772
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/db3622d8-a864-4506-b9e3-46659eb93e3c
-- statement:
--   Find $f: Z \to Z$ such that: $3f(x)-2f(f(x))=x$ $\forall x \in Z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48772 : ∃ f : ℤ → ℤ, ∀ x : ℤ, 3 * f x - 2 * f (f x) = x   :=  by sorry
