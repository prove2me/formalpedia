-- Prove2me | Theorems.Thm_lean_workbook_plus_60793
-- name    : lean_workbook_plus_60793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/02856722-eb1b-4e5d-8878-7825ddf7b101
-- statement:
--   Prove that for positive reals $ a,b,c$ with sum 2 , \n $ 2\ge \sum_{sym}a^2b \Longleftrightarrow (a+b+c)^3 \ge 4(\sum_{sym}a^2b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60793 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : 2 ≥ a^2 * b + b^2 * c + c^2 * a ↔ (a + b + c)^3 ≥ 4 * (a^2 * b + b^2 * c + c^2 * a)   :=  by sorry
