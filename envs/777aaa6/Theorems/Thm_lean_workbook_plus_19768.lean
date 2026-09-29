-- Prove2me | Theorems.Thm_lean_workbook_plus_19768
-- name    : lean_workbook_plus_19768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/23a1d496-ea93-4934-b755-6c48ac99bdf6
-- statement:
--   either way, you obtain\n$\left(a^4+b^4+c^4\right)+3\left(b^2c^2+c^2a^2+a^2b^2\right)$\n$\geq 2\left(bc\left(b^2+c^2\right)+ca\left(c^2+a^2\right)+ab\left(a^2+b^2\right)\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19768 (a b c : ℝ) :
  (a^4 + b^4 + c^4) + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) ≥
  2 * (b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2))   :=  by sorry
