-- Prove2me | solution 1 for lean_workbook_plus_17704
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:50.036821+00:00
-- url     : https://prove2.me/submissions/345dce8d-9da5-45d7-a06e-f3fde107d741

import Mathlib.Analysis.Complex.Basic

theorem solution :
  ∀ a b c a₂ b₂ c₂ : ℝ,
    a * (b + c₂) + b * (c + a₂) + c * (a + b₂) = a₂ * (b + c) + b₂ * (c + a) + c₂ * (a + b) ↔
    a * b + b * c + c * a = a₂ * c + b₂ * a + c₂ * b := by
  intro a b c a₂ b₂ c₂
  constructor <;> intro h <;> linarith
