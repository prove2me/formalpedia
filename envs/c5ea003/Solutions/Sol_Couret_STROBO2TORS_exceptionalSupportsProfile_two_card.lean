-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupportsProfile_two_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:56.468934+00:00
-- url     : https://prove2.me/submissions/5926fe21-9a54-419a-9274-382b4cfabaed

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_one_card
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_injective_on_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/





/-- No raw exceptional parameter is repeated: profile counts can be
computed as *parameter* counts without counting an orbit or fibre twice. -/
theorem exceptionalSupportsProfile_card_eq_params (j : ℕ) :
    (exceptionalSupportsProfile (G := G) j).card =
      (exceptionalParamsProfile (G := G) j).card := by
  rw [exceptionalSupportsProfile_eq_params_image]
  apply Finset.card_image_iff.mpr
  intro p hp q hq heq
  exact paramSupport_injective_on_exceptionalParams
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 heq

/-! ## Arithmetic classification of each exceptional parameter profile -/

/-- In the exceptional normal form, precisely the singleton lies in G[2]
if and only if the parameter a itself has order dividing two. -/
theorem paramSupport_profile_one_iff (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (paramSupport ((a, d), v) ∩ (twoTorsion : Finset G)).card = 1 ↔
      a ∈ (twoTorsion : Finset G) := by
  rw [paramSupport_inter_twoTorsion_card a d v hd hd0 hv hv0, mem_twoTorsion]
  by_cases ha : a + a = 0
  · simp [ha]
  · by_cases hb : (a + v) + (a + v) = 0
    · simp [ha, hb]
    · simp [ha, hb]

/-- Exactly two support vertices belong to G[2] if and only if a+v does. -/
theorem paramSupport_profile_two_iff (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (paramSupport ((a, d), v) ∩ (twoTorsion : Finset G)).card = 2 ↔
      a + v ∈ (twoTorsion : Finset G) := by
  rw [paramSupport_inter_twoTorsion_card a d v hd hd0 hv hv0, mem_twoTorsion]
  have hdiff := exceptional_param_genuine a v hv hv0
  by_cases ha : a + a = 0
  · have hb : (a + v) + (a + v) ≠ 0 :=
      fun h => hdiff (ha.trans h.symm)
    simp [ha, hb]
  · by_cases hb : (a + v) + (a + v) = 0
    · simp [ha, hb]
    · simp [ha, hb]



/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/

/-- Exchange the singleton and paired two-torsion cosets and reverse the
three-torsion direction. The parameter involution does not identify
distinct exceptional supports. -/
private def exceptionalParamFlip (p : (G × G) × G) : (G × G) × G :=
  ((p.1.1 + p.2, p.1.2), -p.2)

private theorem exceptionalParamFlip_involutive (p : (G × G) × G) :
    exceptionalParamFlip (exceptionalParamFlip p) = p := by
  rcases p with ⟨⟨a, d⟩, v⟩
  simp [exceptionalParamFlip, add_assoc]

private theorem exceptionalParamFlip_two_to_one (p : (G × G) × G)
    (hp : p ∈ (exceptionalParamsProfile (G := G) 2)) :
    exceptionalParamFlip p ∈ (exceptionalParamsProfile (G := G) 1) := by
  rcases p with ⟨⟨a, d⟩, v⟩
  obtain ⟨hPar, hTwo⟩ := Finset.mem_filter.mp hp
  obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hPar
  have hvNeg : ((-v) + (-v)) + (-v) = 0 := by
    calc
      ((-v) + (-v)) + (-v) = -((v + v) + v) := by abel
      _ = 0 := by rw [hv]; simp
  have hvNeg0 : -v ≠ 0 := neg_ne_zero.mpr hv0
  change (((a + v, d), -v) : (G × G) × G) ∈
    (exceptionalParamsProfile (G := G) 1)
  apply Finset.mem_filter.mpr
  constructor
  · exact (mem_exceptionalParams (a + v) d (-v)).mpr ⟨hd, hd0, hvNeg, hvNeg0⟩
  · exact (paramSupport_profile_one_iff (a + v) d (-v)
      hd hd0 hvNeg hvNeg0).mpr
      ((paramSupport_profile_two_iff a d v hd hd0 hv hv0).mp hTwo)

private theorem exceptionalParamFlip_one_to_two (p : (G × G) × G)
    (hp : p ∈ (exceptionalParamsProfile (G := G) 1)) :
    exceptionalParamFlip p ∈ (exceptionalParamsProfile (G := G) 2) := by
  rcases p with ⟨⟨a, d⟩, v⟩
  obtain ⟨hPar, hOne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hPar
  have hvNeg : ((-v) + (-v)) + (-v) = 0 := by
    calc
      ((-v) + (-v)) + (-v) = -((v + v) + v) := by abel
      _ = 0 := by rw [hv]; simp
  have hvNeg0 : -v ≠ 0 := neg_ne_zero.mpr hv0
  have ha : a ∈ (twoTorsion : Finset G) :=
    (paramSupport_profile_one_iff a d v hd hd0 hv hv0).mp hOne
  change (((a + v, d), -v) : (G × G) × G) ∈
    (exceptionalParamsProfile (G := G) 2)
  apply Finset.mem_filter.mpr
  constructor
  · exact (mem_exceptionalParams (a + v) d (-v)).mpr ⟨hd, hd0, hvNeg, hvNeg0⟩
  · apply (paramSupport_profile_two_iff (a + v) d (-v)
      hd hd0 hvNeg hvNeg0).mpr
    simpa [add_assoc] using ha

private theorem exceptionalParamsProfile_two_flip_eq_one :
    ((exceptionalParamsProfile (G := G) 2).image exceptionalParamFlip) =
      exceptionalParamsProfile (G := G) 1 := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    rw [← hqp]
    exact exceptionalParamFlip_two_to_one q hq
  · intro hp
    exact Finset.mem_image.mpr ⟨exceptionalParamFlip p,
      exceptionalParamFlip_one_to_two p hp,
      exceptionalParamFlip_involutive p⟩

/-- The second exceptional-profile support count equals the first one.
This is a count of supports, not fibres. -/
theorem p2m_local_exceptionalSupportsProfile_two_card :
    (exceptionalSupportsProfile (G := G) 2).card =
      (twoTorsion : Finset G).card *
        ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by
  have hImageCard :
      ((exceptionalParamsProfile (G := G) 2).image exceptionalParamFlip).card =
        (exceptionalParamsProfile (G := G) 2).card := by
    apply Finset.card_image_iff.mpr
    intro p hp q hq hpq
    have hh := congrArg exceptionalParamFlip hpq
    simpa only [exceptionalParamFlip_involutive] using hh
  calc
    (exceptionalSupportsProfile (G := G) 2).card =
        (exceptionalParamsProfile (G := G) 2).card :=
          exceptionalSupportsProfile_card_eq_params 2
    _ = ((exceptionalParamsProfile (G := G) 2).image exceptionalParamFlip).card :=
      hImageCard.symm
    _ = (exceptionalParamsProfile (G := G) 1).card :=
      congrArg Finset.card exceptionalParamsProfile_two_flip_eq_one
    _ = (exceptionalSupportsProfile (G := G) 1).card :=
      (exceptionalSupportsProfile_card_eq_params 1).symm
    _ = _ := exceptionalSupportsProfile_one_card

/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupportsProfile_two_card

