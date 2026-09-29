-- Prove2me | Theorems.Thm_lean_workbook_plus_22774
-- name    : lean_workbook_plus_22774
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9eb56a81-ec72-41f5-8acb-adfe300ee564
-- statement:
--   Prove that if $a, b \in \mathbb{R}$, then $ab > 0$ if both $a$ and $b$ have the same sign.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22774 (a b : ℝ) : (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) → a * b > 0   :=  by sorry
