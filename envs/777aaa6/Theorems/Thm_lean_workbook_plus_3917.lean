-- Prove2me | Theorems.Thm_lean_workbook_plus_3917
-- name    : lean_workbook_plus_3917
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6a45f5ce-c861-476a-81c6-c16254a688f1
-- statement:
--   By the Rearrangement Theorem, prove that $ x^{2}+y^{2}+z^{2} \geq xy + yz + zx$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3917 (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x   :=  by sorry
