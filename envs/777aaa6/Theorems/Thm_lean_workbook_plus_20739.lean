-- Prove2me | Theorems.Thm_lean_workbook_plus_20739
-- name    : lean_workbook_plus_20739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/af732bb4-c89d-4dce-b720-50ceb9ccf09c
-- statement:
--   Let $a,b,c>0$ . Prove that : $(2) \frac{a}{{b + \frac{869}{320}c}} + \frac{b}{{c + a}}+ \frac{c}{{a + b}} \ge \frac{239}{205}$ When does the equality hold ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (b + (869 / 320) * c) + b / (c + a) + c / (a + b) ≥ 239 / 205)   :=  by sorry
