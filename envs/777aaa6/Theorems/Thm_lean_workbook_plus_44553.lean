-- Prove2me | Theorems.Thm_lean_workbook_plus_44553
-- name    : lean_workbook_plus_44553
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7ec8e94b-8bb5-41e1-bf59-2367cf8cd151
-- statement:
--   Given the polynomial $2003x^{2}+2004x+2004=0$, find the sum of its roots.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44553 : 2003 * x^2 + 2004 * x + 2004 = 0 → x₁ + x₂ = -2004/2003   :=  by sorry
