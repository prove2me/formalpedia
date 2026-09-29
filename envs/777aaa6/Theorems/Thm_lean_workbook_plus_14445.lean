-- Prove2me | Theorems.Thm_lean_workbook_plus_14445
-- name    : lean_workbook_plus_14445
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e700e1be-e90e-4344-9a57-8bfba1fa6f72
-- statement:
--   prove that: \n\n $ab^4c+bc^4d+acd^4+a^4bd \geq abcd(a^2+c^2+b^2+d^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14445 : ∀ a b c d : ℝ, a * b ^ 4 * c + b * c ^ 4 * d + a * c * d ^ 4 + a ^ 4 * b * d ≥ a * b * c * d * (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2)   :=  by sorry
