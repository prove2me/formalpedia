-- Prove2me | Theorems.Thm_lean_workbook_plus_65330
-- name    : lean_workbook_plus_65330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f49c2a6c-13cc-4e8b-8344-e9680d07f997
-- statement:
--   Let a,b,c,d be four positive real numbers. Prove that $ (a - b)(b - c)(c - d)(d - a) + (a - c)^{2}(b - d)^{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65330 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :  (a - b) * (b - c) * (c - d) * (d - a) + (a - c) ^ 2 * (b - d) ^ 2 ≥ 0   :=  by sorry
