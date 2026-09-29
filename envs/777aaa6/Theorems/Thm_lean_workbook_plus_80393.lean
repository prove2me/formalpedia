-- Prove2me | Theorems.Thm_lean_workbook_plus_80393
-- name    : lean_workbook_plus_80393
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e0a3e681-cd8a-44c7-bd4f-3a97cdf95d59
-- statement:
--   Prove, that $x^2+y^2+z^2=xy+yz+zx$ if and only if x=y=z.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80393 (x y z: ℝ) : x^2 + y^2 + z^2 = x * y + y * z + z * x ↔ x = y ∧ y = z ∧ z = x   :=  by sorry
