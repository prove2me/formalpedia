-- Prove2me | Theorems.Thm_lean_workbook_plus_73589
-- name    : lean_workbook_plus_73589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d7a5d4d9-0080-4c08-a330-c847af8cc883
-- statement:
--   Prove that $a^2+b^2+c^2=9$ given $a+b+c=5$ and $ab+bc+ca=8$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73589 (a b c : ℝ) (h₁ : a + b + c = 5) (h₂ : a * b + b * c + c * a = 8) : a ^ 2 + b ^ 2 + c ^ 2 = 9   :=  by sorry
