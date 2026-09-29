-- Prove2me | Theorems.Thm_lean_workbook_plus_70978
-- name    : lean_workbook_plus_70978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d2e58de2-08c7-4054-8688-dd7dbd7425f1
-- statement:
--   prove $\frac{a}{a^{3}+4}\leq \frac{2a+3}{25}$ for non-negative $a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70978 (a : ℝ) (ha : 0 ≤ a) : a / (a^3 + 4) ≤ (2*a + 3) / 25   :=  by sorry
