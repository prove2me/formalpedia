-- Prove2me | Theorems.Thm_lean_workbook_plus_4097
-- name    : lean_workbook_plus_4097
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c001d022-226b-4616-b62d-4c19eb77d48a
-- statement:
--   $=2R^{2}\sin \alpha [\sin(\alpha+\theta)\sin(2\alpha+\theta)-\sin \theta \sin(3\alpha+\theta)]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4097 (R α θ : ℝ) : R^2 * (sin α * (sin (α + θ) * sin (2 * α + θ) - sin θ * sin (3 * α + θ))) = R^2 * (sin α * (sin (α + θ) * sin (2 * α + θ) - sin θ * sin (3 * α + θ)))   :=  by sorry
