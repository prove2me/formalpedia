-- Prove2me | Theorems.Thm_lean_workbook_plus_40888
-- name    : lean_workbook_plus_40888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/85a0761f-61fc-41a7-a245-d5cfa14c6c58
-- statement:
--   Prove by induction that $f(n) = f(1) + n - 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40888 (f : ℕ → ℕ) (n : ℕ) (h₁ : f 1 = 1) (h₂ : ∀ n, f (n + 1) = f n + 1) : f n = f 1 + n - 1   :=  by sorry
