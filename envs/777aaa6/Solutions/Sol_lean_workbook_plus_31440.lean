-- Prove2me | solution 1 for lean_workbook_plus_31440
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:50.271809+00:00
-- url     : https://prove2.me/submissions/14fe3e3c-8338-4e4c-9498-42fc91711916

import Mathlib

set_option autoImplicit false

theorem solution : ({0, 1, 4, 7} : Set Nat) =
    {n : Nat | n < 9 ∧ ∃ k : Nat, k < 9 ∧ (n : Int) ≡ (k : Int)^2 [ZMOD 9]} := by
  ext n
  constructor
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨by decide, 0, by decide, by decide⟩
    · exact ⟨by decide, 1, by decide, by decide⟩
    · exact ⟨by decide, 2, by decide, by decide⟩
    · exact ⟨by decide, 4, by decide, by decide⟩
  · rintro ⟨hn, k, hk, hmod⟩
    interval_cases n <;> interval_cases k <;>
      norm_num [Set.mem_insert_iff, Set.mem_singleton_iff, Int.ModEq] at *

#print axioms solution
