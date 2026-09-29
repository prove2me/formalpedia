-- Prove2me | Theorems.Thm_lean_workbook_plus_52386
-- name    : lean_workbook_plus_52386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/363e8916-632b-4085-9245-0095810f0ba1
-- statement:
--   Prove that if $a^2 + b^2 = c^2$ and $0<a<b<c$, then $a+b>c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52386 {a b c : ℝ} (h₁ : a^2 + b^2 = c^2) (h₂ : 0 < a ∧ 0 < b ∧ 0 < c) (h₃ : a < b) (h₄ : b < c) : a + b > c   :=  by sorry
