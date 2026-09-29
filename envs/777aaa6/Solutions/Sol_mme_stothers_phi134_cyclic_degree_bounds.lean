-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_degree_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:42:04.833581+00:00
-- url     : https://prove2.me/submissions/1cc0c733-9f1a-4cb0-a989-a0ca8e18063b

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi134_exact_profile_card
import Theorems.Thm_mme_stothers_phi134_cyclic_mode_fiber_card

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true

namespace MME.StothersFourth.Phi134DegreeBounds

private noncomputable def addressLabel
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem addressLabel_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (addressLabel x hx j) :=
  Classical.choose_spec (hx j)

private theorem pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private theorem label_injective
    (N alpha beta gamma delta : ℕ) :
    Function.Injective
      (fun w : ExactProfileAddress N alpha beta gamma delta ↦
        fun j ↦ addressLabel w.1.1 w.1.2.1 j) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  have hsx := congrFun (addressLabel_spec x.1.1 x.1.2.1 j) i
  have hsy := congrFun (addressLabel_spec y.1.1 y.1.2.1 j) i
  have hj := congrFun h j
  exact hsx.trans
    ((congrArg (fun r ↦ pattern r i) hj).trans hsy.symm)

private theorem profile_total
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    ∑ r : Fin 8, profileMultiplicity alpha beta gamma delta r = 2 * N := by
  simp [profileMultiplicity, Fin.sum_univ_succ]
  omega

end MME.StothersFourth.Phi134DegreeBounds

/-- The sharp cyclic same-mode degree is positive and bounded by the
exponential envelope used by the prime--Behrend selector. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    1 ≤ D 0 * (D 1 * D 2) ∧
      D 0 * (D 1 * D 2) ≤ 5 ^ (12 * N) := by
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
  letI : Fintype (ExactProfileAddress N alpha beta gamma delta) :=
    exactProfileAddressFintype N alpha beta gamma delta
  letI : Fintype (CyclicExactEdge N alpha beta gamma delta) :=
    cyclicExactEdgeFintype N alpha beta gamma delta
  have htarget : 0 < Nat.card
      (ExactProfileAddress N alpha beta gamma delta) := by
    rw [mme_stothers_phi134_exact_profile_card
      N alpha beta gamma delta hsum]
    have hh := Nat.multinomial_pos Finset.univ
      (profileMultiplicity alpha beta gamma delta)
    simpa only [Nat.multinomial,
      MME.StothersFourth.Phi134DegreeBounds.profile_total
        N alpha beta gamma delta hsum] using hh
  obtain ⟨w⟩ := (Nat.card_pos_iff.mp htarget).1
  let e : CyclicExactEdge N alpha beta gamma delta := (w, (w, w))
  let F := {f : CyclicExactEdge N alpha beta gamma delta //
    cyclicModeWord f 0 = cyclicModeWord e 0}
  have heq : Nat.card F = degree := by
    have h := mme_stothers_phi134_cyclic_mode_fiber_card
      N alpha beta gamma delta hsum e 0
    simpa only [F, degree] using h
  have hpos : 0 < Nat.card F :=
    (Nat.card_pos_iff).mpr ⟨⟨⟨e, rfl⟩⟩, inferInstance⟩
  have hle : Nat.card F ≤
      Nat.card (CyclicExactEdge N alpha beta gamma delta) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hw : Nat.card (ExactProfileAddress N alpha beta gamma delta) ≤
      8 ^ (2 * N) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (ExactProfileAddress N alpha beta gamma delta) ≤
          Fintype.card (Fin (2 * N) → Fin 8) :=
        Fintype.card_le_of_injective
          (fun w j ↦
            MME.StothersFourth.Phi134DegreeBounds.addressLabel
              w.1.1 w.1.2.1 j)
          (MME.StothersFourth.Phi134DegreeBounds.label_injective
            N alpha beta gamma delta)
      _ = 8 ^ (2 * N) := by simp
  have hc : Nat.card (CyclicExactEdge N alpha beta gamma delta) =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
    simp [CyclicExactEdge, pow_succ]
    ring
  change 1 ≤ degree ∧ degree ≤ 5 ^ (12 * N)
  refine ⟨by rw [← heq]; omega, ?_⟩
  rw [← heq]
  calc
    Nat.card F ≤ Nat.card
        (CyclicExactEdge N alpha beta gamma delta) := hle
    _ ≤ (8 ^ (2 * N)) ^ 3 := by
      rw [hc]
      exact Nat.pow_le_pow_left hw 3
    _ = 8 ^ (6 * N) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ 25 ^ (6 * N) := Nat.pow_le_pow_left (by omega) _
    _ = 5 ^ (12 * N) := by
      rw [show (25 : ℕ) = 5 ^ 2 by norm_num, ← pow_mul]
      congr 1
      omega
