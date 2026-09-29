-- Prove2me | Theorems.Thm_lean_workbook_plus_45996
-- name    : lean_workbook_plus_45996
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/09c48be9-2c76-4c6c-9978-3adf3a26113e
-- statement:
--   Lagrange: $(a^2+b^2)(c^2+d^2) = (ac-bd)^2+(ad+bc)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45996 (a b c d : ℂ) : (a^2+b^2)*(c^2+d^2) = (a*c-b*d)^2+(a*d+b*c)^2   :=  by sorry
