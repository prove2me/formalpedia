-- Prove2me | Theorems.Thm_lean_workbook_plus_60138
-- name    : lean_workbook_plus_60138
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/7cc90c6c-9edb-406d-a6ab-923c44dc184d
-- statement:
--   Let $ 0\le{a}\le{b}\le{c} $ be real numbers. Prove that $ (a+3b)(b+4c)(c+2a)\ge {60abc} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60138 (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry
