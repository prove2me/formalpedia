-- Prove2me | Theorems.Thm_lean_workbook_plus_73106
-- name    : lean_workbook_plus_73106
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d916b5a6-dd07-4c72-94df-3a89da3c69e9
-- statement:
--   $\sin (2C)<\sin(2B)$ is equivalent to $\sin(B-C)\cdot \cos A<0.\ (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73106 : ∀ (A B C : ℝ), (Real.sin (2 * C) < Real.sin (2 * B)) ↔ (Real.sin (B - C) * Real.cos A < 0)   :=  by sorry
