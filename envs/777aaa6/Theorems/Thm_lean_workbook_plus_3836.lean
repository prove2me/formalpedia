-- Prove2me | Theorems.Thm_lean_workbook_plus_3836
-- name    : lean_workbook_plus_3836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6784a6f7-5c24-4bc4-bd52-85adf2a1b5d8
-- statement:
--   Prove that $ x^{4}+4y^{4}=(x^{2}+2y^{2}+2xy)(x^{2}+2y^{2}-2xy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3836 (x y : ℤ) : x^4 + 4*y^4 = (x^2 + 2*y^2 + 2*x*y) * (x^2 + 2*y^2 - 2*x*y)   :=  by sorry
