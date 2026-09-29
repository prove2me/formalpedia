-- Prove2me | solution 1 for mme_CW_2376_exact_profile_address_nat_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:15:23.778072+00:00
-- url     : https://prove2.me/submissions/7a122ffb-31ab-404d-ba2f-a7388ed43af2

import Definitions.Def_mme_CW_2376_joint_profile_table
import Theorems.Thm_mme_CW_2376_profile_multiplicity_sum
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open MME BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Exact multinomial cardinality of the optimized fifteen-cell CW profile. -/
theorem solution (m : ℕ) :
    Nat.card (CW2376ExactProfileAddress m) =
      (cw2376ProfileLength m).factorial /
        ∏ sigma : CW2376SupportedJointType,
          (cw2376TargetJointTable m sigma).factorial := by
  classical
  letI : Fintype (CW2376ProfileAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (cw2376ProfileLength m) → Fin 5))
  letI : Fintype (CW2376ExactProfileAddress m) :=
    inferInstanceAs (Fintype
      {a : CW2376ProfileAddress m //
        ∀ sigma : Fin 3 → Fin 5,
          (Finset.univ.filter
            (fun j => cw2376AddressType a j = sigma)).card =
              cw2376ProfileMultiplicity m sigma})
  let e : CW2376ProfileAddress m ≃
      (Fin (cw2376ProfileLength m) → (Fin 3 → Fin 5)) := {
    toFun := fun a j i => a i j
    invFun := fun g i j => g j i
    left_inv := by intro a; rfl
    right_inv := by intro g; rfl
  }
  have hcardFiber
      (g : Fin (cw2376ProfileLength m) → (Fin 3 → Fin 5))
      (sigma : Fin 3 → Fin 5) :
      Fintype.card {j // g j = sigma} =
        (Finset.univ.filter (fun j => g j = sigma)).card := by
    rw [Fintype.card_subtype]
  let eExact : CW2376ExactProfileAddress m ≃
      {g : Fin (cw2376ProfileLength m) → (Fin 3 → Fin 5) //
        ∀ sigma, Fintype.card {j // g j = sigma} =
          cw2376ProfileMultiplicity m sigma} :=
    Equiv.subtypeEquiv e (fun a => by
      constructor
      · intro ha sigma
        rw [hcardFiber]
        simpa only [e, cw2376AddressType] using ha sigma
      · intro hg sigma
        have h := hg sigma
        rw [hcardFiber] at h
        simpa only [e, cw2376AddressType] using h)
  have hcount := mme_fintype_prescribed_fiber_function_card
    (α := Fin (cw2376ProfileLength m))
    (ι := Fin 3 → Fin 5)
    (cw2376ProfileMultiplicity m)
    (by simpa using mme_CW_2376_profile_multiplicity_sum m)
  have hzero : ∀ sigma : Fin 3 → Fin 5,
      sigma ∉ cw2376TargetJointTypes →
        cw2376ProfileMultiplicity m sigma = 0 := by
    intro sigma hsigma
    have hs : sigma ∉ cw2376ScalarTypes := by
      intro h
      exact hsigma (by simp [cw2376TargetJointTypes, h])
    have hr : sigma ∉ cw2376RectTypes := by
      intro h
      exact hsigma (by simp [cw2376TargetJointTypes, h])
    have hc : sigma ∉ cw2376CentralTypes := by
      intro h
      exact hsigma (by simp [cw2376TargetJointTypes, h])
    have hd : sigma ∉ cw2376CoupledTypes := by
      intro h
      exact hsigma (by simp [cw2376TargetJointTypes, h])
    simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
  have hden :
      (∏ sigma : Fin 3 → Fin 5,
          (cw2376ProfileMultiplicity m sigma).factorial) =
        ∏ sigma : CW2376SupportedJointType,
          (cw2376TargetJointTable m sigma).factorial := by
    have hout :
        (∏ sigma ∈ (cw2376TargetJointTypesᶜ : Finset (Fin 3 → Fin 5)),
          (cw2376ProfileMultiplicity m sigma).factorial) = 1 := by
      apply Finset.prod_eq_one
      intro sigma hsigma
      have hsigma' : sigma ∉ cw2376TargetJointTypes := by
        simpa only [Finset.mem_compl, Finset.mem_univ, true_and] using hsigma
      rw [hzero sigma hsigma']
      rfl
    calc
      (∏ sigma : Fin 3 → Fin 5,
          (cw2376ProfileMultiplicity m sigma).factorial) =
          (∏ sigma ∈ cw2376TargetJointTypes,
            (cw2376ProfileMultiplicity m sigma).factorial) *
          ∏ sigma ∈ (cw2376TargetJointTypesᶜ : Finset (Fin 3 → Fin 5)),
            (cw2376ProfileMultiplicity m sigma).factorial := by
        exact (Finset.prod_mul_prod_compl cw2376TargetJointTypes
          (fun sigma => (cw2376ProfileMultiplicity m sigma).factorial)).symm
      _ = ∏ sigma ∈ cw2376TargetJointTypes,
            (cw2376ProfileMultiplicity m sigma).factorial := by
        rw [hout, mul_one]
      _ = ∏ sigma : CW2376SupportedJointType,
          (cw2376TargetJointTable m sigma).factorial := by
        simpa only [cw2376TargetJointTable] using
          (Finset.prod_subtype cw2376TargetJointTypes
            (fun sigma => Iff.rfl)
            (fun sigma => (cw2376ProfileMultiplicity m sigma).factorial))
  rw [Nat.card_eq_fintype_card, Fintype.card_congr eExact]
  simpa only [Fintype.card_fin, hden] using hcount
