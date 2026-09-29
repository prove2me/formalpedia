-- Prove2me | Theorems.Thm_lean_workbook_plus_73592
-- name    : lean_workbook_plus_73592
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/801eb1a3-4979-4a90-ba91-ebb96ff054f6
-- statement:
--   Prove that $1+a^2+a^4 \geq \frac{1}{3a^2}(a+a^2+a^3)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73592 : ∀ a : ℝ, 1 + a^2 + a^4 ≥ 1 / (3 * a^2) * (a + a^2 + a^3)   :=  by sorry
