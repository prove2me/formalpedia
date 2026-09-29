-- Prove2me | Theorems.Thm_lean_workbook_plus_47972
-- name    : lean_workbook_plus_47972
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ee415506-b41e-4fae-a4b0-b97ef0b535b7
-- statement:
--   Let $ ABC$ be an triangle . Prove or disprove that \n $ 4\cos(\frac {A}{2})\cos(\frac {B}{2})\cos(\frac {C}{2})\ge\sin(A + B + C)$ . \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47972 (A B C : ℝ) (hx: A > 0 ∧ B > 0 ∧ C > 0) (hab : A + B + C = π) : 4 * Real.cos (A / 2) * Real.cos (B / 2) * Real.cos (C / 2) ≥ Real.sin (A + B + C)   :=  by sorry
