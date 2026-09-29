-- Prove2me | Theorems.Thm_lean_workbook_plus_80657
-- name    : lean_workbook_plus_80657
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b4413f25-e5fe-4f51-bf7f-a0400d7d150c
-- statement:
--   Find $\cos(2\alpha+2\theta)$ using double angle identities if $\cos(2\alpha) = \frac{7}{25}$ and $\sin(2\alpha) = \frac{24}{25}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80657 (α θ : ℝ) (h₁ : cos (2 * α) = 7 / 25) (h₂ : sin (2 * α) = 24 / 25) : cos (2 * α + 2 * θ) = (7 * cos (2 * θ) - 24 * sin (2 * θ)) / 25   :=  by sorry
