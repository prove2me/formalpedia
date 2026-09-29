-- Prove2me | Theorems.Thm_lean_workbook_plus_42346
-- name    : lean_workbook_plus_42346
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fce3a421-0415-41a6-a575-e749cfce11a0
-- statement:
--   $ab+bc+ca=(ab+bc-ca)+(bc+ca-ab)+(ab+ac-bc) \geq a^2+b^2+c^2,$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42346 : ∀ a b c : ℝ, a * b + b * c + c * a = (a * b + b * c - c * a) + (b * c + c * a - a * b) + (a * b + a * c - b * c) ∧ (a * b + b * c - c * a) + (b * c + c * a - a * b) + (a * b + a * c - b * c) ≥ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
