-- Prove2me | Theorems.Thm_lean_workbook_plus_47893
-- name    : lean_workbook_plus_47893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/63cdf8b9-bd4f-498e-8c8e-b8224e211ea3
-- statement:
--   $$ a(1-b)+b(1-c)+c(1-d)+d(1-a)\le2$$ for all $0\leq a,b,c,d\leq1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47893 (a b c d : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) : a * (1 - b) + b * (1 - c) + c * (1 - d) + d * (1 - a) ≤ 2   :=  by sorry
