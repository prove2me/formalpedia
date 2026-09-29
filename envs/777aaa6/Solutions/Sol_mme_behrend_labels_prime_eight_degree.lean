-- Prove2me | solution 1 for mme_behrend_labels_prime_eight_degree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T18:40:43.397432+00:00
-- url     : https://prove2.me/submissions/1abbb6cb-e934-465f-9681-bde5b707ee4b

import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree

set_option autoImplicit false

theorem solution (N D d : ℕ) (hD1 : 1 ≤ D) (hD5 : D ≤ 5 ^ N) (hdD : d ≤ D) :
    ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (6 * D : ℝ) ≤ (S.card : ℝ) ∧
        8 * d ≤ p := by
  obtain ⟨p, hp, h5, S, hsub, hfree, hcard, -⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree N D hD1 hD5
  have hle : S.card ≤ p / 2 := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_range] at h
  have h6 : 6 * D ≤ S.card := by exact_mod_cast hcard
  have h8 : 8 * d ≤ p := by omega
  exact ⟨p, hp, h5, S, hsub, hfree, hcard, h8⟩
