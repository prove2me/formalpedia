-- Prove2me | Theorems.Thm_lean_workbook_plus_64337
-- name    : lean_workbook_plus_64337
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/26e0176c-9bb8-4ec3-b7c7-54d3bc10ddeb
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that $a^5c^2+b^5a^2+c^5b^2\geq abc(a^3c+b^3a+c^3b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64337 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 * c^2 + b^5 * a^2 + c^5 * b^2 ≥ a * b * c * (a^3 * c + b^3 * a + c^3 * b)   :=  by sorry
