-- Prove2me | Theorems.Thm_lean_workbook_plus_35738
-- name    : lean_workbook_plus_35738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/d5e3c160-00dc-4f25-a6e6-e56fc807f17b
-- statement:
--   Prove for any nonnegative reals $a,b,c$ : $a^{3}b^{2}+b^{3}c^{2}+c^{3}a^{2}\ge a^{2}b^{2}c+ab^{2}c^{2}+a^{2}bc^{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35738 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ≥ a^2 * b^2 * c + a * b^2 * c^2 + a^2 * b * c^2   :=  by sorry
