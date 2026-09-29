-- Prove2me | solution 1 for mme_stothers_phi233_behrend_prime_of_ambient_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T08:52:46.866812+00:00
-- url     : https://prove2.me/submissions/33c1e3b1-850d-41cf-a0aa-e5f25ebdcd5e

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_ambient_star_crude_bounds
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-- Behrend/prime selection for the actual ambient degree of a cyclic
`phi_233` exact address, with labels cast into `ZMod p`. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : ExactProfileAddress N alpha beta gamma delta) :
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧
      ∃ S : Finset (ZMod p),
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
          x + y = 2 * z → x = z ∧ z = y) ∧
        6 *
            ((∏ l : Fin 3,
              Nat.card
                {b : MarginalAddress N alpha beta gamma delta //
                  b.1 l = a.1.1 l}) : ℝ) ≤
          (S.card : ℝ) ∧
        (p : ℝ) ≤
          ((∏ l : Fin 3,
              Nat.card
                {b : MarginalAddress N alpha beta gamma delta //
                  b.1 l = a.1.1 l}) : ℝ) *
            Real.exp (2000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ))) := by
  classical
  let D : ℕ := ∏ l : Fin 3,
    Nat.card
      {b : MarginalAddress N alpha beta gamma delta //
        b.1 l = a.1.1 l}
  obtain ⟨hD1raw, hD5raw⟩ :=
    mme_stothers_phi233_ambient_star_crude_bounds
      N alpha beta gamma delta a
  have hD1 : 1 ≤ D := by simpa [D] using hD1raw
  have hD5 : D ≤ 5 ^ (18 * N) := by simpa [D] using hD5raw
  obtain ⟨p, hpPrime, hp5, Sold, hSrange, hSfree, hSsix, hpScaled⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree
      (18 * N) D hD1 hD5
  have hp7 : 7 ≤ p := by
    -- S ⊆ range (p/2) and |S| ≥ 6 force p ≥ 12.
    have hScardSix : 6 ≤ Sold.card := by
      have : (6 : ℝ) ≤ (Sold.card : ℝ) := by
        calc
          (6 : ℝ) ≤ (6 * D : ℝ) := by
            exact_mod_cast Nat.mul_le_mul_left 6 hD1
          _ ≤ (Sold.card : ℝ) := hSsix
      exact_mod_cast this
    have hScardHalf : Sold.card ≤ p / 2 :=
      (Finset.card_le_card hSrange).trans_eq (Finset.card_range _)
    omega
  obtain ⟨hcard, hAPcast⟩ :=
    mme_stothers_phi233_lower_half_cast_label_package p Sold hSrange hSfree
  let S : Finset (ZMod p) := Sold.image (fun s : ℕ => (s : ZMod p))
  refine ⟨p, hpPrime, hp7, S, hAPcast, ?_, ?_⟩
  · have hScard : (S.card : ℝ) = (Sold.card : ℝ) := by
      exact_mod_cast hcard
    have hsix : 6 * (D : ℝ) ≤ (Sold.card : ℝ) := hSsix
    simpa [D, hScard] using hsix
  · simpa [D] using hpScaled
