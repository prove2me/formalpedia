-- Prove2me | Theorems.Thm_WorkbookSource_plus_63221
-- name    : WorkbookSource.plus_63221
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:39:07.473718+00:00
-- url     : https://prove2.me/theorems/44aca95f-786d-4b89-a025-80a02ca1423c
-- title:
--   A fourth-order recurrence grows slower than the square of its index
-- statement:
--   Let a₀=a₁=a₃=0 and a₂=−1, with aₙ₊₄+2aₙ₊₃+3aₙ₊₂+2aₙ₊₁+aₙ=0 for every n≥0. Then lim aₙ/n²=0.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_63221 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63221; Apache-2.0

import Mathlib

theorem WorkbookSource.plus_63221 (a : ℕ → ℝ) (a0 : a 0 = 0) (a1 : a 1 = 0) (a2 : a 2 = -1) (a3 : a 3 = 0) (h : ∀ n, a (n + 4) + 2 * a (n + 3) + 3 * a (n + 2) + 2 * a (n + 1) + a n = 0) : ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |a n / n ^ 2| < ε   :=  by sorry
