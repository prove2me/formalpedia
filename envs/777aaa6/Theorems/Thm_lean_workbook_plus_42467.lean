-- Prove2me | Theorems.Thm_lean_workbook_plus_42467
-- name    : lean_workbook_plus_42467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/82900519-b71d-4451-8609-7389a63a6f18
-- statement:
--   Let $a,b,c \in R$ prove that: $a^2+b^2+c^2-ab-bc-ca\geq\frac{3}{4}(a-b)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42467 (a b c : ℝ) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ (3 / 4) * (a - b)^2   :=  by sorry
