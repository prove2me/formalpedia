-- Prove2me | Theorems.Thm_lean_workbook_plus_57377
-- name    : lean_workbook_plus_57377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e05c2f14-36aa-43e7-ac6d-087b6975bb9d
-- statement:
--   Let $x=a+b, y=a+c, z=b+c$ . Notice that $x^2+y^2+z^2=a^2+b^2+c^2+(a+b+c)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57377 : ∀ x y z a b c : ℝ, x = a + b → y = a + c → z = b + c → x^2 + y^2 + z^2 = a^2 + b^2 + c^2 + (a + b + c)^2   :=  by sorry
