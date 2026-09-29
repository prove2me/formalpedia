-- Prove2me | Theorems.Thm_lean_workbook_plus_21729
-- name    : lean_workbook_plus_21729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/cf96cafc-9eda-416a-ba6d-98934222868e
-- statement:
--   Prove that if $a, b, c$ are integers such that $a + b + c = 0$, then $47$ divides $a^{47} + b^{47} + c^{47}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21729 {a b c : ℤ} (h : a + b + c = 0) : 47 ∣ a ^ 47 + b ^ 47 + c ^ 47   :=  by sorry
