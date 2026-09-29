-- Prove2me | Theorems.Thm_lean_workbook_plus_65034
-- name    : lean_workbook_plus_65034
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/fbc7c4cd-8fc0-470a-b985-238cc19ea874
-- statement:
--   Solution (One-liner) $\frac{\binom{6}{3} - \binom{4}{3}}{\binom{6}{3}} = \frac{20 - 4}{20} = \frac{16}{20} = \boxed{\frac{4}{5}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65034 :
  ((Nat.choose 6 3) - (Nat.choose 4 3)) / (Nat.choose 6 3) = 4 / 5   :=  by sorry
