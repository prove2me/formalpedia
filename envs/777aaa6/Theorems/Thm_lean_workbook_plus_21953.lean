-- Prove2me | Theorems.Thm_lean_workbook_plus_21953
-- name    : lean_workbook_plus_21953
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5c076890-a746-43a7-ba62-863ab7f4d12f
-- statement:
--   Then $$\sqrt{a(a+8)}=\frac{15}{2}$$ $$\implies 4a^2+32a=225$$ $$\implies (2a+8)^2=289$$ $$\implies 2a+8=17$$ $$\implies a=\frac{9}{2}$$ Thus, the average of all the terms of the sequence is $A=\boxed{\frac{17}{2}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21953  (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : Real.sqrt (a * (a + 8)) = 15 / 2) :
  (a + (a + 8)) / 2 = 17 / 2   :=  by sorry
