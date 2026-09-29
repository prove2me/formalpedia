-- Prove2me | Theorems.Thm_lean_workbook_plus_71316
-- name    : lean_workbook_plus_71316
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d2f4763f-07df-479f-bcc5-c34ea08fcaa4
-- statement:
--   By AM-GM, we have $\frac{a + b + c}{3} \geq \sqrt[3]{abc}$ , so $a + b + c \geq \sqrt[3]{27abc}$ and $(a + b + c)^3 \geq 27abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71316  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  (a + b + c)^3 ≥ 27 * a * b * c   :=  by sorry
