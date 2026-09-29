-- Prove2me | Theorems.Thm_lean_workbook_plus_57944
-- name    : lean_workbook_plus_57944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/291de795-36d8-4ff0-bd72-08a6c2aeaa74
-- statement:
--   $a,b,c>0\iff x,y,z>0$ doesn't make difference. If the inequality $\sum{\sqrt{x^{2}+y^{2}+2z}}<\sqrt{3}$ doesn't hold for $\left( x,y,z \right) = \left( 1,0,0 \right)$ , it also doesn't hold for $\left( x,y,z\right) = \left( 1-\varepsilon,\frac{\varepsilon}{2},\frac{\varepsilon}{2}\right)$ , where $\varepsilon>0$ is near $0$ (and such triples satisfy condition $x,y,z>0$ ), so the inequality $\sum{\sqrt{x^{2}+y^{2}+2z}}<\sqrt{3}$ isn't true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57944 :
  ¬∀ x y z : ℝ, (x > 0 ∧ y > 0 ∧ z > 0 → √(x^2 + y^2 + 2 * z) + √(y^2 + z^2 + 2 * x) + √(z^2 + x^2 + 2 * y) < √3)   :=  by sorry
