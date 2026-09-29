-- Prove2me | Theorems.Thm_lean_workbook_plus_44620
-- name    : lean_workbook_plus_44620
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ae7d3f91-22b6-4de7-9fda-8eb7c7c6f6ad
-- statement:
--   $ f(2n) = 2n - 1$ $ \forall n > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44620 (f : ℕ → ℕ) (hf: ∀ n, n > 0 → f (2 * n) = 2 * n - 1) : ∀ n, n > 0 → f (2 * n) = 2 * n - 1   :=  by sorry
