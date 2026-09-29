-- Prove2me | Theorems.Thm_lean_workbook_plus_1269
-- name    : lean_workbook_plus_1269
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b29eddca-9808-493e-b8a3-fd7259f49638
-- statement:
--   P3 $\sqrt{abc}(a+b+c-2)\ge \frac{2\left(1-3abc-\left(\sqrt{bc}\right)^3-\left(\sqrt{ca}\right)^3-\left(\sqrt{ab}\right)^3\right)}{\sqrt{a}+\sqrt{b}+\sqrt{c}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1269 : ∀ a b c : ℝ, (Real.sqrt a * Real.sqrt b * Real.sqrt c) * (a + b + c - 2) ≥ (2 * (1 - 3 * a * b * c - (Real.sqrt (b * c))^3 - (Real.sqrt (c * a))^3 - (Real.sqrt (a * b))^3)) / (Real.sqrt a + Real.sqrt b + Real.sqrt c)   :=  by sorry
