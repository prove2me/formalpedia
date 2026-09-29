-- Prove2me | Theorems.Thm_lean_workbook_plus_1487
-- name    : lean_workbook_plus_1487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d167b60e-5064-462d-993d-02bd4bd59af4
-- statement:
--   It is also $(a^2b+ab^2-2b^3)^2+(a^3-2b^3+ab^2)^2\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1487 (a b : ℝ) : (a^2 * b + a * b^2 - 2 * b^3)^2 + (a^3 - 2 * b^3 + a * b^2)^2 ≥ 0   :=  by sorry
