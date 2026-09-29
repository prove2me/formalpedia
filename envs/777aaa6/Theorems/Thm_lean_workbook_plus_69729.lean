-- Prove2me | Theorems.Thm_lean_workbook_plus_69729
-- name    : lean_workbook_plus_69729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a0df5d9e-fdef-4c06-b742-ce116940580e
-- statement:
--   $\lfloor x\rfloor \le x < \lfloor x\rfloor + 1, \quad \forall x \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69729 (x : ℝ) : ⌊x⌋ ≤ x ∧ x < ⌊x⌋ + 1   :=  by sorry
