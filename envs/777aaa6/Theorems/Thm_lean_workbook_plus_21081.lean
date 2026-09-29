-- Prove2me | Theorems.Thm_lean_workbook_plus_21081
-- name    : lean_workbook_plus_21081
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4f1036af-ce9f-49f2-b5a3-304eb6e893a1
-- statement:
--   If $\cos(\theta - \alpha) = p$ and $\sin(\theta + \beta) = q$ then prove that $ p^2 + q^2 - 2pq \sin(\alpha + \beta) = \cos^2 (\alpha + \beta) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21081 (θ α β p q : ℝ) (hp : p = Real.cos (θ - α)) (hq : q = Real.sin (θ + β)) : p^2 + q^2 - 2 * p * q * Real.sin (α + β) = Real.cos (α + β)^2   :=  by sorry
