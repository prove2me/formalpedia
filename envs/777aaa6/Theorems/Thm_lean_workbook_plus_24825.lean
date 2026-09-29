-- Prove2me | Theorems.Thm_lean_workbook_plus_24825
-- name    : lean_workbook_plus_24825
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3a4e5135-82b6-49fe-a82a-5725ff1d954d
-- statement:
--   Prove that $ f^{-1}(C\cap D) = f^{-1}(C)\cap f^{-1}(D)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24825 (f : X → Y) (A B : Set Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B   :=  by sorry
