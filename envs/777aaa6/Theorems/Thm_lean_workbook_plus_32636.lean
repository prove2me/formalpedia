-- Prove2me | Theorems.Thm_lean_workbook_plus_32636
-- name    : lean_workbook_plus_32636
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8787821e-8fd4-4707-94a2-db8bda55bf2d
-- statement:
--   For all real numbers $ a,b,c$ with $ 0 < a,b,c < 1$ is: $ \sqrt{abc}+\sqrt{(1-a)(1-b)(1-c)}<3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32636 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :  Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) < 3   :=  by sorry
