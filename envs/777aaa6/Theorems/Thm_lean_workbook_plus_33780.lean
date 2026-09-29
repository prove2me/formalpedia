-- Prove2me | Theorems.Thm_lean_workbook_plus_33780
-- name    : lean_workbook_plus_33780
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1a526ee2-5765-4636-b943-63b0d6714528
-- statement:
--   Prove that $ 4(x^{6}+y^{6}+z^{6})\geq 4(x^{3}y^{3}+y^{3}z^{3}+z^{3}x^{3})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33780 (x y z : ℝ) : 4 * (x^6 + y^6 + z^6) ≥ 4 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3)   :=  by sorry
