-- Prove2me | Theorems.Thm_lean_workbook_plus_82815
-- name    : lean_workbook_plus_82815
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.51614+00:00
-- url     : https://prove2.me/theorems/5e2232d3-fad8-4de6-b1c4-3f2471188ff5
-- statement:
--   Prove the equality: $|z1 - z2|^2 + |z2 - z3|^2 + |z3 - z1|^2 + |z1 + z2 + z3|^2 = 3(|z1|^2 + |z2|^2 + |z3|^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82815 (z1 z2 z3 : ℂ) : 
  Complex.abs (z1 - z2) ^ 2 + Complex.abs (z2 - z3) ^ 2 + Complex.abs (z3 - z1) ^ 2 + Complex.abs (z1 + z2 + z3) ^ 2 =
  3 * (Complex.abs z1 ^ 2 + Complex.abs z2 ^ 2 + Complex.abs z3 ^ 2)   :=  by sorry
