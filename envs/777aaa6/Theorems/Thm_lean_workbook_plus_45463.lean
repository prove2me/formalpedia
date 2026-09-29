-- Prove2me | Theorems.Thm_lean_workbook_plus_45463
-- name    : lean_workbook_plus_45463
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a07e0f70-a809-46cf-9df9-abf954e427b3
-- statement:
--   $ \frac{p_{1}}{p_{2}}+\frac{p_{2}}{p_{1}}=\frac{p_{1}^{2}+p_{2}^{2}}{p_{1}p_{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45463 (p₁ p₂ : ℝ) : p₁ / p₂ + p₂ / p₁ = (p₁ ^ 2 + p₂ ^ 2) / (p₁ * p₂)   :=  by sorry
