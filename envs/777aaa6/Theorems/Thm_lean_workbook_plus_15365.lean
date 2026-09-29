-- Prove2me | Theorems.Thm_lean_workbook_plus_15365
-- name    : lean_workbook_plus_15365
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ecc38d47-18c0-462c-b0f0-3c1f973394ac
-- statement:
--   If $sinA+sinB+sinC=0$ and $sin^3A+sin^3B+sin^3C=0$, prove that: $cos(2A)cos(2B)cos(2C) \geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15365 (A B C : ℝ) (hA : 0 < A ∧ A <= π ∧ A <= 2 * π) (hB : 0 < B ∧ B <= π ∧ B <= 2 * π) (hC : 0 < C ∧ C <= π ∧ C <= 2 * π) (hA2 : A + B + C = π) (hA3 : sin A + sin B + sin C = 0) (hA4 : sin A ^ 3 + sin B ^ 3 + sin C ^ 3 = 0) : cos (2 * A) * cos (2 * B) * cos (2 * C) >= 0   :=  by sorry
