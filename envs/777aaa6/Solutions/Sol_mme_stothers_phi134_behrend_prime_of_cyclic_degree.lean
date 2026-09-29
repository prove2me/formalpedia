-- Prove2me | solution 1 for mme_stothers_phi134_behrend_prime_of_cyclic_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:40:23.474802+00:00
-- url     : https://prove2.me/submissions/be0f3b37-0a04-4059-a9cf-a136beedf247

import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_stothers_phi134_cyclic_degree_bounds
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package

open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

/-- A prime and progression-free label set large enough for the sharp
Phi134 cyclic collision degree, with the explicit subexponential bound. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧
      ∃ S : Finset (ZMod p),
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
          x + y = 2 * z → x = z ∧ z = y) ∧
        6 * (D 0 * (D 1 * D 2) : ℝ) ≤ S.card ∧
        (p : ℝ) ≤ (D 0 * (D 1 * D 2) : ℝ) *
          Real.exp (2000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) := by
  classical
  dsimp only
  let degree : ℕ :=
    (∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta 0 s).factorial /
          ∏ r : {r : Fin 8 // pattern r 0 = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial) *
      ((∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta 1 s).factorial /
            ∏ r : {r : Fin 8 // pattern r 1 = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial) *
        (∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta 2 s).factorial /
            ∏ r : {r : Fin 8 // pattern r 2 = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial))
  have hbounds := mme_stothers_phi134_cyclic_degree_bounds
    N alpha beta gamma delta hsum
  change 1 ≤ degree ∧ degree ≤ 5 ^ (12 * N) at hbounds
  obtain ⟨p, hp, hp5, Sold, hSrange, hSfree, hSbig, hpbound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree
      (12 * N) degree hbounds.1 hbounds.2
  have hcard := Finset.card_le_card hSrange
  rw [Finset.card_range] at hcard
  have hSbigNat : 6 * degree ≤ Sold.card := by
    exact_mod_cast hSbig
  have hSix : 6 ≤ Sold.card := by omega
  have hp7 : 7 ≤ p := by omega
  obtain ⟨hcastcard, hcastfree⟩ :=
    mme_stothers_phi233_lower_half_cast_label_package
      p Sold hSrange hSfree
  refine ⟨p, hp, hp7,
    Sold.image (fun s : ℕ ↦ (s : ZMod p)), hcastfree, ?_, ?_⟩
  · rw [hcastcard]
    simp only [degree, Nat.cast_mul] at hSbig
    exact hSbig
  · simp only [degree, Nat.cast_mul] at hpbound
    exact hpbound
