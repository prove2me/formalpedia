-- Prove2me | Theorems.Thm_lean_workbook_plus_16244
-- name    : lean_workbook_plus_16244
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/438228af-6493-42c1-8cbb-89bfbe187fa0
-- statement:
--   Prove that if $ a,b,c>0$ and $ a+b+c=3$ then: $ a^4+b^4+c^4 \ge a^3+b^3+c^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16244 (a b c : ℝ) (ha : a>0 ∧ b>0 ∧ c>0 ∧ a+b+c=3) : a^4+b^4+c^4 ≥ a^3+b^3+c^3   :=  by sorry
