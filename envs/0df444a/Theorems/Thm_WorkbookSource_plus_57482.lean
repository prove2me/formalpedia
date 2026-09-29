-- Prove2me | Theorems.Thm_WorkbookSource_plus_57482
-- name    : WorkbookSource.plus_57482
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:27:13.280268+00:00
-- url     : https://prove2.me/theorems/de3d1165-ad4a-459f-8fbf-8ee7b105e142
-- title:
--   Boundedness of a square-root averaging recurrence
-- statement:
--   A real sequence satisfies 2xₙ=xₙ₋₁+√(3−3xₙ₋₁²). Then it is bounded: some real M satisfies |xₙ|<M for every natural index n.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_57482 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_57482; Apache-2.0

import Mathlib

theorem WorkbookSource.plus_57482 (x : ℕ → ℝ) (hx: ∀ n, 2*x n = x (n-1) + Real.sqrt (3 - 3*(x (n-1))^2)) : ∃ M, ∀ n, |x n| < M   :=  by sorry
