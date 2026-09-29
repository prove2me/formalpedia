-- Prove2me | Theorems.Thm_lean_workbook_plus_54146
-- name    : lean_workbook_plus_54146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1e5de146-5f4b-4838-811d-6a28856747e8
-- statement:
--   Prove that for real nos. $ a,b,c > 2$ the relation holds good: $ a + b + c < abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54146 (a b c : ℝ) (ha : 2 < a) (hb : 2 < b) (hc : 2 < c) : a + b + c < a * b * c   :=  by sorry
