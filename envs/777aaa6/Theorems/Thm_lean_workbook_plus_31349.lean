-- Prove2me | Theorems.Thm_lean_workbook_plus_31349
-- name    : lean_workbook_plus_31349
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f570b425-3842-4211-815d-f63ab8053450
-- statement:
--   Prove that $ (\frac {p - 1}{2})^2 + \frac {p - 1}{2} + 1 = \frac {p^2 + 3}{4} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31349  (p : ℕ)
  (h₀ : p > 0)
  (h₁ : p % 2 = 1) :
  ((p - 1) / 2)^2 + (p - 1) / 2 + 1 = (p^2 + 3) / 4   :=  by sorry
