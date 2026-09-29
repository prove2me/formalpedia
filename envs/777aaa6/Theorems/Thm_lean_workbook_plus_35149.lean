-- Prove2me | Theorems.Thm_lean_workbook_plus_35149
-- name    : lean_workbook_plus_35149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a216f3e2-18b3-4139-9c60-3a0c6a57d911
-- statement:
--   Prove for non-negative $a$ and $b$ that $(a+b)(a^4+b^4)\geq (a^2+b^2)(a^3+b^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35149 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) * (a ^ 4 + b ^ 4) ≥ (a ^ 2 + b ^ 2) * (a ^ 3 + b ^ 3)   :=  by sorry
