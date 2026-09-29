-- Prove2me | Theorems.Thm_lean_workbook_plus_54058
-- name    : lean_workbook_plus_54058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fabd30a8-4bdc-4cf4-832d-83d3dac2210f
-- statement:
--   Lemma: \n\n $$(a^2+2bc)(b^2+2ca)(c^2+2ab)=(a^2+b^2+c^2)(ab+bc+ca)^2-(a-b)^2(b-c)^2(c-a)^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54058 (a b c : ℝ) :
  (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) =
  (a^2 + b^2 + c^2) * (a * b + b * c + c * a)^2 - (a - b)^2 * (b - c)^2 * (c - a)^2   :=  by sorry
