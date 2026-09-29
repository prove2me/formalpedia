-- Prove2me | Theorems.Thm_lean_workbook_plus_33967
-- name    : lean_workbook_plus_33967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c01e5982-e81e-4938-a617-deb713ffff7f
-- statement:
--   Prove that for the function $f(x)=|x|$, $f\left(\frac{a+b}{2}\right)\le \frac{f(a)+f(b)}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33967 (a b : ℝ) : |(a + b) / 2| ≤ (|a| + |b|) / 2   :=  by sorry
