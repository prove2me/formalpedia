-- Prove2me | Theorems.Thm_lean_workbook_plus_61552
-- name    : lean_workbook_plus_61552
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cd508121-f47d-4104-98d9-7d94892a4904
-- statement:
--   Prove that $a^5+b^5+c^5 \ge \frac{1}{27} (a+b+c)^3 (a^2+b^2+c^2) \ge abc(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61552 : ∀ a b c : ℝ, a ^ 5 + b ^ 5 + c ^ 5 ≥ (1 / 27) * (a + b + c) ^ 3 * (a ^ 2 + b ^ 2 + c ^ 2) ∧ (1 / 27) * (a + b + c) ^ 3 * (a ^ 2 + b ^ 2 + c ^ 2) >= a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
