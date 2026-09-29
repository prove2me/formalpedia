-- Prove2me | Theorems.Thm_lean_workbook_plus_32246
-- name    : lean_workbook_plus_32246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9537a3ca-9e6e-4397-b362-f20e005fa47e
-- statement:
--   Or, by AM-GM, $ a^{100} + b^{100} \geq 2 \sqrt{a^{100} \cdot b^{100}} = 2(ab)^{50}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32246  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  a^100 + b^100 ≥ 2 * (a * b)^50   :=  by sorry
