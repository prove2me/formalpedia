-- Prove2me | Theorems.Thm_lean_workbook_plus_6169
-- name    : lean_workbook_plus_6169
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/69a67a0c-8a3b-4f68-a311-02a33e28e239
-- statement:
--   Let $a = 25^{12}$ , $b = 16^{14}$ , and $c = 11^{16} $ . Arrange $a$ , $b$ , and $c$ in descending order.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6169 (a b c : ℝ) (ha : a = 25^12) (hb : b = 16^14) (hc : c = 11^16) : b > a ∧ a > c   :=  by sorry
