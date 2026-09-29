-- Prove2me | Theorems.Thm_lean_workbook_plus_8890
-- name    : lean_workbook_plus_8890
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/45dc78f9-8980-4216-8a05-0e6140619f56
-- statement:
--   Let $ a+b-c=x $\nb+c-a=y \nc+a-b=z \nSo we get $ (x+y)/2=b $ \n$ (z+y)/2= c $ \n$ (x+z)/2=a $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8890 (a b c x y z : ℝ) : a + b - c = x ∧ b + c - a = y ∧ c + a - b = z → (x + y) / 2 = b ∧ (z + y) / 2 = c ∧ (x + z) / 2 = a   :=  by sorry
