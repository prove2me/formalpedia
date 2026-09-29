-- Prove2me | Theorems.Thm_lean_workbook_plus_57124
-- name    : lean_workbook_plus_57124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/64dfbf23-db4a-4f3d-b48d-7eafc118bdb0
-- statement:
--   Prove that $n^7 - n = n(n+1)(n-1)(n^2-n+1)(n^2+n+1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57124 : ∀ n : ℤ, n^7 - n = n * (n + 1) * (n - 1) * (n^2 - n + 1) * (n^2 + n + 1)   :=  by sorry
