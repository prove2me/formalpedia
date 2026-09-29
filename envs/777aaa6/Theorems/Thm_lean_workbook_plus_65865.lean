-- Prove2me | Theorems.Thm_lean_workbook_plus_65865
-- name    : lean_workbook_plus_65865
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3807b2bb-77a2-4467-bdb1-8205f6570ffe
-- statement:
--   The answer is the number of positive integers in $\{2,3,\dots,999\}$ not divisible by 2 or 3, which is $998-499-333+166=\boxed{332}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65865 :
  Finset.card (Finset.filter (λ x => ¬ 2∣x ∧ ¬ 3∣x) (Finset.Icc 2 999)) = 332   :=  by sorry
