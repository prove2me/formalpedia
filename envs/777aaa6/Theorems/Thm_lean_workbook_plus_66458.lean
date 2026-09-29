-- Prove2me | Theorems.Thm_lean_workbook_plus_66458
-- name    : lean_workbook_plus_66458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4dc4a099-5441-47b1-b51a-6d90830f8948
-- statement:
--   It remains to check that $17^2 < 13\cdot 11\cdot 7$ and $13^2 < 11\cdot 7\cdot 5$ , which hold (but $11^2 > 7\cdot 5\cdot 3$ , so we need $n\geq 6$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66458 :
  17^2 < 13 * 11 * 7 ∧ 13^2 < 11 * 7 * 5   :=  by sorry
