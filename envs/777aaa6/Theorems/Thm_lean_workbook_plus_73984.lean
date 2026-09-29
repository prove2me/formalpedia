-- Prove2me | Theorems.Thm_lean_workbook_plus_73984
-- name    : lean_workbook_plus_73984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a42b25d3-bcd5-49bb-9099-159afae50c57
-- statement:
--   What if $f(x)=1$ for x=0, and $f(x)=0$ everywhere else?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73984 : ∃ f : ℝ → ℝ, ∀ x, (x = 0 → f x = 1) ∧ (x ≠ 0 → f x = 0)   :=  by sorry
