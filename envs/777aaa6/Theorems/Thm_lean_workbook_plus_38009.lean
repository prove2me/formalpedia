-- Prove2me | Theorems.Thm_lean_workbook_plus_38009
-- name    : lean_workbook_plus_38009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/45425b96-db6a-4d2e-9f7a-5e3c216c5a93
-- statement:
--   $ \sqrt{(a^2+d^2)(b^2+c^2)} \geq (ac+bd)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38009 (a b c d : ℝ) : Real.sqrt ((a^2 + d^2) * (b^2 + c^2)) ≥ a * c + b * d   :=  by sorry
