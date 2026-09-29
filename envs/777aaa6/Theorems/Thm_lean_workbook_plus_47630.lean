-- Prove2me | Theorems.Thm_lean_workbook_plus_47630
-- name    : lean_workbook_plus_47630
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/306323cc-4a1b-4e2b-8007-9e14e6aeeefc
-- statement:
--   ${a}^{2} \left( b-c \right) +{b}^{2} \left( c-a \right) +{c}^{2} \left( a-b \right) = \left( a-b \right) \left( a-c \right) \left( b-c \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47630 {a b c : ℝ} : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) = (a - b) * (a - c) * (b - c)   :=  by sorry
