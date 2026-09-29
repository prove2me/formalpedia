-- Prove2me | Theorems.Thm_lean_workbook_plus_6592
-- name    : lean_workbook_plus_6592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/adc1f33d-424a-43db-9618-ca225df7f6d0
-- statement:
--   If $f(\mathbb R)=\{0\}$ , we get solution $\boxed{\text{S1 : }f(x)=0\text{ }\forall x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6592 (f : ℝ → ℝ): f '' Set.univ = {0} → ∀ x, f x = 0   :=  by sorry
