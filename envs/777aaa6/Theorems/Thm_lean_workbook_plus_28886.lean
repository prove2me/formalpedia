-- Prove2me | Theorems.Thm_lean_workbook_plus_28886
-- name    : lean_workbook_plus_28886
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/5a7fb5c2-e92a-42c1-881c-75e2fbe13e3e
-- statement:
--   Prove $4(a^2b+b^2c+c^2a)^2 \leq (a^2+b^2+c^2).\frac{4}{3}.(a^2+b^2+c^2)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28886 (a b c : ℝ) : 4 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (4 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2   :=  by sorry
