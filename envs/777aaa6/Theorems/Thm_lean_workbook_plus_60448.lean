-- Prove2me | Theorems.Thm_lean_workbook_plus_60448
-- name    : lean_workbook_plus_60448
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d49fae9c-b0da-4b04-bef5-caa6c9b2d3ca
-- statement:
--   Prove $\cos A + \cos B = 2 \cos{\frac{A + B}{2}} \cos{\frac{A - B}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60448 (A B : ℝ) : Real.cos A + Real.cos B = 2 * Real.cos ((A + B) / 2) * Real.cos ((A - B) / 2)   :=  by sorry
