-- Prove2me | Theorems.Thm_lean_workbook_plus_74263
-- name    : lean_workbook_plus_74263
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d9d745ad-8178-4f05-83d6-3dea44c5a52b
-- statement:
--   For any integers $a$ and $b$ , prove that if $a$ divides $b$ then $a^{3}$ divides $b^{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74263 {a b : ℤ} (h₁ : a ∣ b) : a^3 ∣ b^3   :=  by sorry
