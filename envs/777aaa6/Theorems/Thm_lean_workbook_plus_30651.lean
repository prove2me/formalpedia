-- Prove2me | Theorems.Thm_lean_workbook_plus_30651
-- name    : lean_workbook_plus_30651
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a7378413-8710-472d-bf60-dc5d8ff7f137
-- statement:
--   Prove the inequality: $a^2 + b^2 + c^2 +2 abc \geq 2(ab +bc+ca) - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30651 : ∀ a b c : ℝ, a^2 + b^2 + c^2 + 2*a*b*c ≥ 2*(a*b + b*c + c*a) - 1   :=  by sorry
