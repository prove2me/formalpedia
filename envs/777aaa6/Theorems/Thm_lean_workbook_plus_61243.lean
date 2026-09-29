-- Prove2me | Theorems.Thm_lean_workbook_plus_61243
-- name    : lean_workbook_plus_61243
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8bcc0d8e-e226-40f8-8685-7c2cab755439
-- statement:
--   $ab^{2}+bc^{2}+ca^{2}\leq \frac{(a+b+c)(a^{2}+b^{2}+c^{2})}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61243 : ∀ a b c : ℝ, a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≤ (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) / 3   :=  by sorry
