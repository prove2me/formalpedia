-- Prove2me | solution 1 for lean_workbook_plus_58004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:44.40532+00:00
-- url     : https://prove2.me/submissions/e5bd3dfb-6286-4864-bf51-073a9854fe84

import Mathlib.Analysis.Complex.Basic

theorem solution  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ x : ZMod n, x ≠ 0 → ∃! y, y^2 = x^2) :
  ∀ x : ZMod n, x ≠ 0 → ∀ y : ZMod n, y ≠ 0 → x^2 = y^2 → x = y ∨ x = -y := by
  intro x hx y hy hxy
  left
  obtain ⟨z, hz, huniq⟩ := h₁ x hx
  have h1 : x = z := huniq x rfl
  have h2 : y = z := huniq y hxy.symm
  rw [h1, h2]
