-- Prove2me | Theorems.Thm_lean_workbook_plus_11863
-- name    : lean_workbook_plus_11863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b04a675f-7709-45e8-b305-7e14e7d13d8a
-- statement:
--   Prove the equality $(x+y)(y+z)(z+x)=(x+y+z)(xy+yz+zx)-xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11863 (x y z : ℝ) : (x + y) * (y + z) * (z + x) = (x + y + z) * (x*y + y*z + z*x) - x*y*z   :=  by sorry
