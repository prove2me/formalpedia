-- Prove2me | Theorems.Thm_lean_workbook_plus_71572
-- name    : lean_workbook_plus_71572
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/03a37bee-668b-48c9-bea6-c75b8e4de717
-- statement:
--   Prove that $ tan^2 \left(\frac {A}{2} \right) + tan^2 \left(\frac {B}{2}\right) + tan^2 \left(\frac {C}{2}\right) > 5 \cdot tan \left(\frac {A}{2}\right)tan \left(\frac {B}{2}\right)tan \left(\frac {C}{2}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71572 :
  ∀ A B C : ℝ, A ∈ Set.Ioc 0 (π / 2) ∧ B ∈ Set.Ioc 0 (π / 2) ∧ C ∈ Set.Ioc 0 (π / 2) ∧ A + B + C = π →
    tan A / 2 ^ 2 + tan B / 2 ^ 2 + tan C / 2 ^ 2 > 5 * (tan A / 2 * tan B / 2 * tan C / 2)   :=  by sorry
