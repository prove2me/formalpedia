-- Prove2me | Theorems.Thm_lean_workbook_plus_2614
-- name    : lean_workbook_plus_2614
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/916dfd8a-702c-46f6-8cb9-8703b6d8ebe8
-- statement:
--   If $\cos(\theta - \alpha) = p$ and $\sin(\theta + \beta) = q$ then prove that $ p^2 + q^2 - 2pq \sin(\alpha + \beta) = \cos^2 (\alpha + \beta) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2614 (p q α β θ : ℝ) (hp : cos (θ - α) = p) (hq : sin (θ + β) = q) : p^2 + q^2 - 2 * p * q * sin (α + β) = cos (α + β)^2   :=  by sorry
