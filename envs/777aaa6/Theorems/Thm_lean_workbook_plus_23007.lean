-- Prove2me | Theorems.Thm_lean_workbook_plus_23007
-- name    : lean_workbook_plus_23007
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/323c512d-9a70-43cb-9a5e-9a1f1b12014b
-- statement:
--   Show that if $g(x+y) = g(x)$, then $g(x)$ is constant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23007 (g : ℝ → ℝ) (h : ∀ x y, g (x + y) = g x) : ∃ c, ∀ x, g x = c   :=  by sorry
