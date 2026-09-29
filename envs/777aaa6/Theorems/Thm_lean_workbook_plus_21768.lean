-- Prove2me | Theorems.Thm_lean_workbook_plus_21768
-- name    : lean_workbook_plus_21768
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/fbd91357-1a68-44fc-ad7d-dd9f7928b198
-- statement:
--   Find the coefficients of the Maclaurin series for $f(x) = e^{\arcsin x}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21768 (n : ℕ) : ∃ (f : ℕ → ℝ), e^arcsin x = ∑' n, f n * x ^ n   :=  by sorry
