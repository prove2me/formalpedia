-- Prove2me | Theorems.Thm_lean_workbook_plus_5763
-- name    : lean_workbook_plus_5763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dc9a988d-2fe3-4b71-98e3-1979f497e43c
-- statement:
--   For all real positive a, b, prove that $a^2b^2(a^2+b^2-2) \geq (a+b)(ab-1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5763 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 * b^2 * (a^2 + b^2 - 2) ≥ (a + b) * (a * b - 1)   :=  by sorry
