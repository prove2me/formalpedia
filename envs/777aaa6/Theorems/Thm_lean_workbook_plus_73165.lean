-- Prove2me | Theorems.Thm_lean_workbook_plus_73165
-- name    : lean_workbook_plus_73165
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/3f9c491c-cc3e-4e96-b0ab-0543e0c08710
-- statement:
--   Prove that \( a^ab^bc^c\ge\left(\frac {a + b + c}{3}\right)^{a + b + c} \) for \( a,b,c\in R^ +\) such that \( a + b + c = 1\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73165 :
    ∀ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 → a^a * b^b * c^c ≥ (a + b + c) ^ (a + b + c)   :=  by sorry
