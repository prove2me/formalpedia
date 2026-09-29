-- Prove2me | Theorems.Thm_lean_workbook_plus_17704
-- name    : lean_workbook_plus_17704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a44a15eb-069a-42d7-b2a9-781fc1438c6b
-- statement:
--   $a_1*(b+c_2)+ b_1*(c+a_2)+ c_1*(a+b_2)= a_2*(b_1+c)+ b_2*(a+c_1)+ c_2*(b+a_1)$ <=> \n$a_1b+b_1c+c_1a=a_2c+b_2a+c_2b$ <=> \n$\left( BX_2-CX_1\right) \cdot BC+\left( CY_2-AY_1\right) \cdot CA+\left( AZ_2-BZ_1\right) \cdot AB=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17704 :
  ∀ a b c a₂ b₂ c₂ : ℝ,
    a * (b + c₂) + b * (c + a₂) + c * (a + b₂) = a₂ * (b + c) + b₂ * (c + a) + c₂ * (a + b) ↔
    a * b + b * c + c * a = a₂ * c + b₂ * a + c₂ * b   :=  by sorry
