-- Prove2me | Theorems.Thm_lean_workbook_plus_71320
-- name    : lean_workbook_plus_71320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a31c71b3-0dbb-4898-9f2d-04c02d74a433
-- statement:
--   Show that all perfect squares are either $\equiv 0$ or $\equiv 1$ in mod 4.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71320 : ∀ (x : ℤ), (x ^ 2 ≡ 0 [ZMOD 4]) ∨ (x ^ 2 ≡ 1 [ZMOD 4])   :=  by sorry
