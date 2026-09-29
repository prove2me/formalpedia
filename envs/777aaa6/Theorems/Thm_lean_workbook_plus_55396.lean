-- Prove2me | Theorems.Thm_lean_workbook_plus_55396
-- name    : lean_workbook_plus_55396
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fcc40f3a-f19d-4d55-ade5-eb267584d4df
-- statement:
--   Prove that $f(z) = z^2$ for all integers $z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55396 (f : ℤ → ℤ) (hf: f = fun z => z^2) : ∀ z : ℤ, f z = z^2   :=  by sorry
