-- Prove2me | Theorems.Thm_lean_workbook_plus_67496
-- name    : lean_workbook_plus_67496
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e2cdbf44-7926-4740-9449-73e39b6d5de7
-- statement:
--   Derive the identity $\cos(\alpha) + \cos(\beta) = 2\cos\left(\frac{\alpha + \beta}{2}\right)\cos\left(\frac{\alpha - \beta}{2}\right)$ using complex numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67496 (α β : ℝ) : Real.cos α + Real.cos β =
    2 * Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2)   :=  by sorry
