-- Prove2me | Theorems.Thm_lean_workbook_plus_19439
-- name    : lean_workbook_plus_19439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/be126042-7578-42dc-8fb0-016454c25e32
-- statement:
--   We have $a^3-b^3=25(a-b),b^3-c^3=49(b-c),c^3-a^3=64(c-a)$ . Add them up to get $8b+5c=13a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19439 (a b c : ℝ) (h : a^3 - b^3 = 25 * (a - b)) (h' : b^3 - c^3 = 49 * (b - c)) (h'' : c^3 - a^3 = 64 * (c - a)) : 8 * b + 5 * c = 13 * a   :=  by sorry
