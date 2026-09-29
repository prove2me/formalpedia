-- Prove2me | Theorems.Thm_lean_workbook_plus_76714
-- name    : lean_workbook_plus_76714
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/06f5acdc-9f13-4fe7-97d5-ccaa783df9d9
-- statement:
--   Show that for all $ a+b<180$ the following inequality holds: $ \frac{\sin ^2 (a) +\sin ^2 (b)}{2}\le 1-\cos a \cos b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76714 (a b : ℝ) (ha : 0 < a ∧ a < π / 2) (hb : 0 < b ∧ b < π / 2) (hab : a + b < π / 2) : (sin a ^ 2 + sin b ^ 2) / 2 ≤ 1 - cos a * cos b   :=  by sorry
