-- Prove2me | Theorems.Thm_lean_workbook_plus_67097
-- name    : lean_workbook_plus_67097
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/099f62fc-f5c5-471b-9255-e77065ae3555
-- statement:
--   Given $b^{2}-ab+{a^{2}\over 4}={b^{2}+c^{2}\over 2}-{a^{2}\over 4}$, prove that $c^{2}=(b-a)^{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67097 : ∀ a b c : ℂ, b^2 - a * b + a^2 / 4 = (b^2 + c^2) / 2 - a^2 / 4 → c^2 = (b - a)^2   :=  by sorry
