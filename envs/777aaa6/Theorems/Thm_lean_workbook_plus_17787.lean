-- Prove2me | Theorems.Thm_lean_workbook_plus_17787
-- name    : lean_workbook_plus_17787
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6143ebee-8727-49b4-b3d6-a2d569f45a6c
-- statement:
--   Let the height of the lamp be $ z$ . Then, using the man's height and length of shadow, we have the ratio $ \frac{z}{x}=\frac{1.8}{6.5} \Rightarrow\frac{z}{20}=\frac{1.8}{6.5}$ , and we get $ z=5.5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17787  (z x : ℝ)
  (h₀ : 0 < z ∧ 0 < x)
  (h₁ : z / x = 1.8 / 6.5)
  (h₂ : x = 20) :
  z = 5.5   :=  by sorry
