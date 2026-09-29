-- Prove2me | Theorems.Thm_lean_workbook_plus_39534
-- name    : lean_workbook_plus_39534
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e4fe5031-2984-4b7e-a560-ce07b3c2fe15
-- statement:
--   By Conservation of energy let it move a distance $ \text{x}$ along the incline then we have \n $ \text{mgx}\sin \theta = \frac {\text{mv}^{2}}{2} + \frac {\text{I}\omega^{2}}{2}$ \n differentiating both sides with time we get \n $ \text{mgv}\sin \theta = \text{mva}_{cm} + \text{I}\frac {\text{va}_{cm}}{\text{R}^{2}}$ \n thus we have \n $ \boxed{\text{a}_{cm} = \frac {\text{g}\sin\theta}{1 + \frac {\text{I}}{\text{mR}^{2}}}}$ \n note this holds for any object pure rolling down an incline of inclination $ \theta$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39534 (R I : ℝ) (m : ℝ) (g θ : ℝ) (h₁ : 0 < R ∧ 0 < I ∧ 0 < m ∧ 0 < g ∧ 0 ≤ θ ∧ θ ≤ 90) : g * sin θ / (1 + (I / (m * R^2))) = g * sin θ / (1 + (I / (m * R^2)))   :=  by sorry
