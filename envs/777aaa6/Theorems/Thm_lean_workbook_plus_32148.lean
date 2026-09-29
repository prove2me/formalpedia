-- Prove2me | Theorems.Thm_lean_workbook_plus_32148
-- name    : lean_workbook_plus_32148
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/98be6d75-f053-4e57-9ade-6d41f5919267
-- statement:
--   $\dfrac{1}{cos^{2}(a)cos^{2}(b)cos^{2}(c)} > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32148 : ∀ a b c : ℝ, (1 / (cos a ^ 2 * cos b ^ 2 * cos c ^ 2)) > 0   :=  by sorry
