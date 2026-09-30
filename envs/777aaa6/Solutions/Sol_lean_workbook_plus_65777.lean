-- Prove2me | solution 1 for lean_workbook_plus_65777
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:37:33.565125+00:00
-- url     : https://prove2.me/submissions/7f50428c-84fd-4582-8f9f-555a745f6495

import Mathlib

set_option autoImplicit false

theorem crt_classification (x : Nat) :
    (x ≡ 5 [ZMOD 7] ∧ x ≡ 7 [ZMOD 11] ∧ x ≡ 3 [ZMOD 13]) ↔
      ∃ k : Nat, x = 1001 * k + 887 := by
  simp only [Int.ModEq]
  constructor
  · intro h
    refine ⟨x / 1001, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    omega

theorem least_solution : IsLeast
    {x : Nat | x ≡ 5 [ZMOD 7] ∧ x ≡ 7 [ZMOD 11] ∧ x ≡ 3 [ZMOD 13]} 887 := by
  constructor
  · norm_num [Set.mem_setOf_eq, Int.ModEq]
  · intro x hx
    obtain ⟨k, hk⟩ := (crt_classification x).mp hx
    omega

theorem solution (x : Nat)
    (hx : x ≡ 5 [ZMOD 7] ∧ x ≡ 7 [ZMOD 11] ∧ x ≡ 3 [ZMOD 13]) : x ≥ 197 := by
  have h := least_solution.2 hx
  omega

#print axioms solution
