-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_behrend_margin_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:21:49.547174+00:00
-- url     : https://prove2.me/submissions/f028982a-bf08-4a9b-8538-f880d4fb58cd

import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_hash_collision_margin

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem solution
    (N Dstar : ℕ) (hDstar : 1 ≤ Dstar)
    (hD5 :
      (6 * (N + 1)) ^ 100 * Dstar ≤ 5 ^ (1000 * N)) :
    let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
    ∃ p : ℕ, p.Prime ∧ 9 ≤ p ∧ Odd p ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (p : ℝ) ^ 2 *
              Real.exp
                (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))) +
            3 * (Dstar : ℝ) * (D : ℝ) ≤
          (Dstar : ℝ) * (S.card : ℝ) := by
  dsimp only
  let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
  have hD1 : 1 ≤ D := by
    dsimp only [D]
    have hP1 : 1 ≤ (6 * (N + 1)) ^ 100 :=
      Nat.one_le_pow 100 (6 * (N + 1)) (by positivity)
    simpa only [one_mul] using Nat.mul_le_mul hP1 hDstar
  obtain ⟨p, hpPrime, _hp5, S, hSrange, hSfree, hSsix, hpScaled⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree
      (1000 * N) D hD1 (by simpa only [D] using hD5)
  have hScardSix : 6 ≤ S.card := by
    have hreal : (6 : ℝ) ≤ (S.card : ℝ) := by
      calc
        (6 : ℝ) ≤ (6 * D : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left 6 hD1
        _ ≤ (S.card : ℝ) := hSsix
    exact_mod_cast hreal
  have hScardHalf : S.card ≤ p / 2 :=
    (Finset.card_le_card hSrange).trans_eq (Finset.card_range _)
  have hp9 : 9 ≤ p := by omega
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
  have hmargin :=
    MME.StothersFourth.mme_stothers_fixed_hash_collision_margin
      N Dstar p S.card
      (by simpa only [D] using hpScaled)
      (by simpa only [D] using hSsix)
  exact ⟨p, hpPrime, hp9, hpOdd, S, hSrange, hSfree, by
    simpa only [D] using hmargin⟩
