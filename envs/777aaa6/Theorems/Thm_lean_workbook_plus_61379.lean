-- Prove2me | Theorems.Thm_lean_workbook_plus_61379
-- name    : lean_workbook_plus_61379
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/377fee2b-227c-4804-bb42-cd0fbd88d8ca
-- statement:
--   By AM-QM: $\frac{a+b+c}{3} \le \sqrt{\frac{a^2+b^2+c^2}{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61379 :
  (a + b + c) / 3 ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3)   :=  by sorry
