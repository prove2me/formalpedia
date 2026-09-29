-- Prove2me | Theorems.Thm_lean_workbook_plus_26836
-- name    : lean_workbook_plus_26836
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6b0077af-838f-4cd6-ac3c-899d5d4eb70c
-- statement:
--   Use the half-angle formula and sum-to-product formula for cosine: $\sin^2(\frac12\alpha)=\frac12(1-\cos\alpha)$ and $\cos A-\cos B=2\sin\left(\frac{-A+B}{2}\right)\sin\left(\frac{A+B}{2}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26836 : ∀ α, sin (α / 2) ^ 2 = (1 - cos α) / 2   :=  by sorry
