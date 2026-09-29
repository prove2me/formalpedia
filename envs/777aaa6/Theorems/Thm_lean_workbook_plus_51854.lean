-- Prove2me | Theorems.Thm_lean_workbook_plus_51854
-- name    : lean_workbook_plus_51854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3906016b-baae-4ce4-8a89-0b7cafc58819
-- statement:
--   where $F \left( a,b,c \right) =\sum \left( \left( a-b \right) ^{2} \left( 1/2\,{a}^{4}+5/2\,{a}^{2}{b}^{2}+1/2\,{b}^{4}+1/2\,{c}^{4} \right) \right) +2\,\sum \left( {a}^{2} \left( a-b \right) ^{2} \left( a-c \right) ^{2} \right) +\sum \left( \left( a-b \right) ^{4}{c}^{2} \right) +5/2\, \left( \prod \left( a-b \right) \right) ^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51854 {a b c : ℝ} : (a - b) ^ 2 * (1 / 2 * a ^ 4 + 5 / 2 * a ^ 2 * b ^ 2 + 1 / 2 * b ^ 4 + 1 / 2 * c ^ 4) + (b - c) ^ 2 * (1 / 2 * b ^ 4 + 5 / 2 * b ^ 2 * c ^ 2 + 1 / 2 * c ^ 4 + 1 / 2 * a ^ 4) + (c - a) ^ 2 * (1 / 2 * c ^ 4 + 5 / 2 * c ^ 2 * a ^ 2 + 1 / 2 * a ^ 4 + 1 / 2 * b ^ 4) + 2 * (a ^ 2 * (a - b) ^ 2 * (a - c) ^ 2 + b ^ 2 * (b - a) ^ 2 * (b - c) ^ 2 + c ^ 2 * (c - a) ^ 2 * (c - b) ^ 2) + (a - b) ^ 4 * c ^ 2 + (b - c) ^ 4 * a ^ 2 + (c - a) ^ 4 * b ^ 2 + 5 / 2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0   :=  by sorry
