-- Prove2me | Theorems.Thm_lean_workbook_plus_6002
-- name    : lean_workbook_plus_6002
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4a940387-bc1d-4a18-93cb-ecdf66b2593f
-- statement:
--   prove that $ x+y+z \leq \sqrt3 $ given $ x^2 + y^2 + z^2 =1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6002 : ∀ x y z : ℝ, x^2 + y^2 + z^2 = 1 → x + y + z ≤ Real.sqrt 3   :=  by sorry
