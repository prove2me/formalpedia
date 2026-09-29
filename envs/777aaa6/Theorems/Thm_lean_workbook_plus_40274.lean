-- Prove2me | Theorems.Thm_lean_workbook_plus_40274
-- name    : lean_workbook_plus_40274
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/891fe698-650b-42d4-9cde-c725e52ae3de
-- statement:
--   by AM-GM $ab\le \frac{a^{2}+b^{2}}{2}$ $ac\le \frac{a^{2}+c^{2}}{2}$ $bc\le \frac{b^{2}+c^{2}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40274 (a b c: ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 ∧ a * c ≤ (a ^ 2 + c ^ 2) / 2 ∧ b * c ≤ (b ^ 2 + c ^ 2) / 2   :=  by sorry
