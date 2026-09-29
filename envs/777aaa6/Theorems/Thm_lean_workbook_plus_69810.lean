-- Prove2me | Theorems.Thm_lean_workbook_plus_69810
-- name    : lean_workbook_plus_69810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/11558652-49d5-4353-b422-7cdce09071cf
-- statement:
--   If $ a, b $ and $ c $ are non-null reals satisfying $ a ^ 2-b ^ 2 = bc $ and $ b ^ 2-c ^ 2 = ac $ . Prove that $ a ^ 2-c ^ 2 = ab $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69810 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ^ 2-b ^ 2 = b*c) (hbc : b ^ 2-c ^ 2 = a*c) : a ^ 2-c ^ 2 = a*b   :=  by sorry
