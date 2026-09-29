-- Prove2me | Theorems.Thm_lean_workbook_plus_44904
-- name    : lean_workbook_plus_44904
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/aeec3c6a-8a96-4609-936e-ff920ec664d6
-- statement:
--   Prove that $2\sin(b)\cos(b) \leq \sin^2(b) + \cos^2(b) = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44904 : 2 * Real.sin b * Real.cos b ≤ Real.sin b ^ 2 + Real.cos b ^ 2 ∧ Real.sin b ^ 2 + Real.cos b ^ 2 = 1   :=  by sorry
