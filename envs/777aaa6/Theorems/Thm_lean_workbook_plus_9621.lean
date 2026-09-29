-- Prove2me | Theorems.Thm_lean_workbook_plus_9621
-- name    : lean_workbook_plus_9621
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d8c40795-59ed-497b-ab86-a225fb93ca58
-- statement:
--   Let $\{a,b,c\}\subset[0,1]$ . Prove that:\na+b+c<=2+abc
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9621 (a b c : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) : a + b + c ≤ 2 + a * b * c   :=  by sorry
