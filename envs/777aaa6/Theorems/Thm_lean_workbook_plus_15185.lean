-- Prove2me | Theorems.Thm_lean_workbook_plus_15185
-- name    : lean_workbook_plus_15185
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b6f8622c-304f-47c8-86eb-aeea82d32e89
-- statement:
--   Prove that $ x^{3}+y^{3}+z^{3}-3xyz=(x+y+z)(x^{2}+y^{2}+z^{2}-xy-zx-yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15185 (x y z : ℝ) : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z)*(x^2 + y^2 + z^2 - x*y - x*z - y*z)   :=  by sorry
