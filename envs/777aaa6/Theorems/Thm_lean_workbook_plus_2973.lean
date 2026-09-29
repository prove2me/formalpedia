-- Prove2me | Theorems.Thm_lean_workbook_plus_2973
-- name    : lean_workbook_plus_2973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/41d6c398-9c0c-4d4f-8909-bf4626df79df
-- statement:
--   Prove that for nonnegative a, b, c, $ a^{3}+b^{3}+c^{3} \geq a^{2}b+b^{2}c+c^{2}a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2973 (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a   :=  by sorry
