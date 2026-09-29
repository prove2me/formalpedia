-- Prove2me | Theorems.Thm_lean_workbook_plus_38742
-- name    : lean_workbook_plus_38742
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2c3ffb02-3e4a-49a6-a694-f65526a1f210
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $(\frac{a}{b}+1)(\frac{a}{c}+1)\ge(\frac{2a}{b+c}+1)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38742 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + 1) * (a / c + 1) ≥ (2 * a / (b + c) + 1) ^ 2   :=  by sorry
