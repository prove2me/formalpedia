-- Prove2me | Theorems.Thm_lean_workbook_plus_71778
-- name    : lean_workbook_plus_71778
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a97f844d-a455-4809-8dc2-bd32e6ab9cf3
-- statement:
--   prove $a^2+b^2+c^2\geq ab+bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71778 : ∀ (a b c : ℝ), a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
