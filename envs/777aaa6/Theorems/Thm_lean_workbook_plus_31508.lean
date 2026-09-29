-- Prove2me | Theorems.Thm_lean_workbook_plus_31508
-- name    : lean_workbook_plus_31508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d48e7096-dae5-44f5-a9d3-0dfe169ec3e5
-- statement:
--   Let $ a,b,c\geq0$ .Prove that: \n $ a^3+b^3+c^3-3abc\geq2(\dfrac{b+c}{2}-a)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31508 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ 2 * ((b + c) / 2 - a)^3   :=  by sorry
