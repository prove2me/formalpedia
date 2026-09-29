-- Prove2me | Theorems.Thm_lean_workbook_plus_34940
-- name    : lean_workbook_plus_34940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c48c9368-629a-4f11-a592-1942f6ca9d38
-- statement:
--   or, show by a longer computation that\n$\left(a^4+b^4+c^4\right)+3\left(b^2c^2+c^2a^2+a^2b^2\right)$\n$-2\left(bc\left(b^2+c^2\right)+ca\left(c^2+a^2\right)+ab\left(a^2+b^2\right)\right)$\n$=\left(a^2+b^2+c^2-bc-ca-ab\right)^2\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34940 :  ∀ a b c : ℝ, (a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) - 2 * (b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2))) = (a^2 + b^2 + c^2 - b * c - c * a - a * b)^2   :=  by sorry
