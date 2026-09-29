-- Prove2me | Theorems.Thm_lean_workbook_plus_11938
-- name    : lean_workbook_plus_11938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b903abcc-1e1f-4ca7-af1c-90ff376212a8
-- statement:
--   Let $a=x-y , b=y-z , c=z-x$ , then we are given that \n $ a^2 + b^2 + c^2 = (a-b)^2 + (b-c)^2 + (c-a)^2 \Rightarrow a^2+ b^2+c^2 -2ab - 2bc - 2ca = 0 $ but as $a+b+c=0 \Rightarrow 2(ab+bc+ca) = - (a^2+b^2+c^2)$ , so \n $ a^2+ b^2+c^2 -2ab - 2bc - 2ca = 0 \Rightarrow a^2 + b^2 + c^2 = 0 \Rightarrow a=b=c=0 $ $ \Rightarrow x=y=z $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11938  (x y z : ℝ)
  (h₀ : x - y = z - x)
  (h₁ : y - z = x - y)
  (h₂ : x - y + y - z + z - x = 0) :
  x - y = 0 ∧ y - z = 0 ∧ z - x = 0   :=  by sorry
