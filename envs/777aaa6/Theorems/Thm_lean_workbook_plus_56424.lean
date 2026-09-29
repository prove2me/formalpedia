-- Prove2me | Theorems.Thm_lean_workbook_plus_56424
-- name    : lean_workbook_plus_56424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ad3d2d44-a3fd-4f6c-ad54-46cf79bcea68
-- statement:
--   $ \frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}\ge \frac{a+b+c}{abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56424 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c)   :=  by sorry
