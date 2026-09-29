-- Prove2me | Theorems.Thm_lean_workbook_plus_37647
-- name    : lean_workbook_plus_37647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7e92f8c6-5e79-47bb-b80b-3d8684e75e6f
-- statement:
--   Prove that $ (ab+bc+ca)^{2}\ge 3abc(a+b+c) = 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37647 (a b c : ℝ) : (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
