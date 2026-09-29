-- Prove2me | Theorems.Thm_lean_workbook_plus_75005
-- name    : lean_workbook_plus_75005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4e5db41a-9b15-4b27-91f8-76a2a76e78cf
-- statement:
--   Let $a,b,c\ge0$ , $abc=1 ,$ prove or disprove that $(1+a^2)(1+b^2)(1+c^2)\ge(1+a)(1+b)(1+c).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75005 (a b c : ℝ) (h1 : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b * c = 1) :
  (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ (1 + a) * (1 + b) * (1 + c)   :=  by sorry
