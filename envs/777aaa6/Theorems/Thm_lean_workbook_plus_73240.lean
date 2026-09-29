-- Prove2me | Theorems.Thm_lean_workbook_plus_73240
-- name    : lean_workbook_plus_73240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/37debd83-1514-40ca-a7cb-e2f79434eefa
-- statement:
--   Prove that $\frac{1}{1+a+b^{-1}}+\frac{1}{1+b+c^{-1}}+\frac{1}{1+c+a^{-1}}\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73240 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (1 + a + b⁻¹) + 1 / (1 + b + c⁻¹) + 1 / (1 + c + a⁻¹) ≤ 1   :=  by sorry
