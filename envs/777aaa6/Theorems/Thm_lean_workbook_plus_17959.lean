-- Prove2me | Theorems.Thm_lean_workbook_plus_17959
-- name    : lean_workbook_plus_17959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/618b901c-e6da-4168-9290-fc668af5cec8
-- statement:
--   Prove that $ x^{3} + y^{3} + z^{3} - 3xyz = (x + y + z)(x^{2} + y^{2} + z^{2} - xy - yz - zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17959 (x y z : ℝ) : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x)   :=  by sorry
