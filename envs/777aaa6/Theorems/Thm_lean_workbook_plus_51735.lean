-- Prove2me | Theorems.Thm_lean_workbook_plus_51735
-- name    : lean_workbook_plus_51735
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1a64f6db-dc89-4ca4-8369-c588827165f6
-- statement:
--   Calculate $(\sqrt{3}^{\sqrt{2})^{\sqrt{2}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51735 : (Real.sqrt 3 ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = Real.sqrt 9   :=  by sorry
