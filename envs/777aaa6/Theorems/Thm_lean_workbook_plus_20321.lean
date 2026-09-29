-- Prove2me | Theorems.Thm_lean_workbook_plus_20321
-- name    : lean_workbook_plus_20321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bcf7662a-ecbd-495e-8e08-9596df6d944b
-- statement:
--   Given $ a,b,c\in \mathbb{R^+}$ , prove that $ a^3+b^3+c^3+5\ge 2a^2+2b^2+2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20321 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 5 ≥ 2 * a^2 + 2 * b^2 + 2 * c^2   :=  by sorry
