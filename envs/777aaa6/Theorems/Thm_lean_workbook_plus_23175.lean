-- Prove2me | Theorems.Thm_lean_workbook_plus_23175
-- name    : lean_workbook_plus_23175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0a1ca04d-7e3d-4c89-b748-b2bc623904dd
-- statement:
--   If $x+y+z = 0$ then $x^3 + y^3 + z^3 = 3xyz$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23175 {x y z : ℂ} (h : x + y + z = 0) : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z   :=  by sorry
