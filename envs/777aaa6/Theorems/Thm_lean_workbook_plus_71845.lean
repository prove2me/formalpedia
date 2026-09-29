-- Prove2me | Theorems.Thm_lean_workbook_plus_71845
-- name    : lean_workbook_plus_71845
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/81491ec5-7243-402c-a4eb-9b90ace3e254
-- statement:
--   The domains of $F_k$ should be $U:={\bf R}^2 \setminus \{(0,0)\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71845 (k : ℤ) (U : Set (ℝ × ℝ)) (hU : U = {p : ℝ × ℝ | p ≠ (0, 0)}) :
  ∀ p : ℝ × ℝ, (p ∈ U ↔ p ≠ (0, 0))   :=  by sorry
