-- Prove2me | Theorems.Thm_lean_workbook_plus_22776
-- name    : lean_workbook_plus_22776
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/539086fa-1276-4eff-ae4d-ec1e85b391a6
-- statement:
--   Find the sum of the positive factors of $32$ (including $32$ itself).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22776 : ∑ i in divisors 32, i = 63   :=  by sorry
