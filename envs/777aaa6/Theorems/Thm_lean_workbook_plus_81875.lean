-- Prove2me | Theorems.Thm_lean_workbook_plus_81875
-- name    : lean_workbook_plus_81875
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/aabb8d70-c67b-4a68-939c-0f6fed2feec0
-- statement:
--   It's equivalent to $ \left(\xi_1 + \xi_2\cos2\varphi_3 + \xi_3\cos2\varphi_2\right)^2 + \left(\xi_2\sin2\varphi_3 - \xi_3\sin2\varphi_2\right)^2\geq0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81875 (ξ₁ ξ₂ ξ₃ φ₂ φ₃ : ℝ) :
  (ξ₁ + ξ₂ * Real.cos (2 * φ₃) + ξ₃ * Real.cos (2 * φ₂)) ^ 2 +
    (ξ₂ * Real.sin (2 * φ₃) - ξ₃ * Real.sin (2 * φ₂)) ^ 2 ≥ 0   :=  by sorry
