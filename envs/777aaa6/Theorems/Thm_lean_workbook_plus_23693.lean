-- Prove2me | Theorems.Thm_lean_workbook_plus_23693
-- name    : lean_workbook_plus_23693
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ccc6bdc0-44bd-42ef-a2e3-8b6f3631deee
-- statement:
--   $g(x) \leqslant g(0) \forall x \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23693 (g : ℝ → ℝ) (hg : ∀ x ≥ 0, g x ≤ g 0) : ∀ x ≥ 0, g x ≤ g 0   :=  by sorry
