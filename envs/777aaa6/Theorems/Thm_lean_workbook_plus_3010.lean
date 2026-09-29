-- Prove2me | Theorems.Thm_lean_workbook_plus_3010
-- name    : lean_workbook_plus_3010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/18fe7d4d-e78c-4e3f-9172-2113986ecd34
-- statement:
--   Prove that if positive real numbers $a, b, c$ satisfies $a+b+c=3$ then $\sqrt{3} \leq \sqrt{a^2+b^2+c^2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3010 : ∀ a b c : ℝ, a + b + c = 3 → Real.sqrt 3 ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
