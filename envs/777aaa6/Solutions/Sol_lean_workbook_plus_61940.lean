-- Prove2me | solution 1 for lean_workbook_plus_61940
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:51.289319+00:00
-- url     : https://prove2.me/submissions/b46d2e6d-0b52-41eb-a80c-1ac2006736a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A₁ A₂ : Set ℕ) (hA₁ : A₁ = {k | k % 2 = 0})
    (hA₂ : A₂ = {k | k % 3 = 0}) : A₁ ∩ A₂ = {k | k % 6 = 0} := by
  ext k
  simp only [hA₁, hA₂, Set.mem_inter_iff, Set.mem_setOf_eq]
  omega

#print axioms solution
