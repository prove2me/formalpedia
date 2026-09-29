-- Prove2me | Theorems.Thm_lean_workbook_plus_62928
-- name    : lean_workbook_plus_62928
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9f456bbe-e256-4c71-a8cc-5581625670e2
-- statement:
--   Suppose that a,b,c are positive numbers. Prove that:\na) $ a^2 b^2 + b^2 c^2 + c^2 a^2 \geq abc(a + b + c)$\nb) If $ a + b + c = 1$ , then $ ab + bc + ca \leq 1/3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62928 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b * c * (a + b + c)   :=  by sorry
