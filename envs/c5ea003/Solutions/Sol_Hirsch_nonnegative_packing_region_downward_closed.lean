-- Prove2me | solution 1 for Hirsch.nonnegative_packing_region_downward_closed
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T18:25:25.996117+00:00
-- url     : https://prove2.me/submissions/3afbc375-ab82-4bcc-aaee-cb0100fad1a3

import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Γ : κ → ι → ℝ) (b : κ → ℝ)
    (hΓ : ∀ j i, 0 ≤ Γ j i) {s t : ι → ℝ}
    (ht_nonnegative : ∀ i, 0 ≤ t i)
    (ht_rows : ∀ j, (∑ i, Γ j i * t i) ≤ b j)
    (hs_nonnegative : ∀ i, 0 ≤ s i)
    (hst : ∀ i, s i ≤ t i) :
    (∀ i, 0 ≤ s i) ∧ ∀ j, (∑ i, Γ j i * s i) ≤ b j := by
  constructor
  · exact hs_nonnegative
  · intro j
    calc
      (∑ i, Γ j i * s i) ≤ ∑ i, Γ j i * t i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hst i) (hΓ j i))
      _ ≤ b j := ht_rows j

#print axioms solution
