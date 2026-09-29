-- Prove2me | solution 1 for Round10.prod_eq_prod_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:37:19.882849+00:00
-- url     : https://prove2.me/submissions/6247a7ed-900b-4aea-9427-090677c8ebc5

import Mathlib
theorem solution : ∀ (P : Finset ℕ) (f g : ℕ → ℕ), (∀ i ∈ P, f i ≤ g i) →
    (∀ i ∈ P, 0 < g i) → ∏ i ∈ P, f i = ∏ i ∈ P, g i → ∀ i ∈ P, f i = g i := by
  intro P f g hle hpos heq i hi
  by_contra hne
  have hlt : f i < g i := lt_of_le_of_ne (hle i hi) hne
  -- the other factors can only shrink, and they stay positive on the `g` side
  have hrest_le : ∏ j ∈ P.erase i, f j ≤ ∏ j ∈ P.erase i, g j :=
    Finset.prod_le_prod' fun j hj => hle j (Finset.mem_of_mem_erase hj)
  have hrest_pos : 0 < ∏ j ∈ P.erase i, g j :=
    Finset.prod_pos fun j hj => hpos j (Finset.mem_of_mem_erase hj)
  rw [← Finset.mul_prod_erase P f hi, ← Finset.mul_prod_erase P g hi] at heq
  -- so one strict factor makes the whole product strictly smaller
  have hstrict : f i * ∏ j ∈ P.erase i, f j < g i * ∏ j ∈ P.erase i, g j :=
    calc f i * ∏ j ∈ P.erase i, f j ≤ f i * ∏ j ∈ P.erase i, g j := Nat.mul_le_mul_left _ hrest_le
      _ < g i * ∏ j ∈ P.erase i, g j := Nat.mul_lt_mul_of_pos_right hlt hrest_pos
  omega
