-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupportsProfile_one_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:32.197859+00:00
-- url     : https://prove2.me/submissions/6b12b638-64d7-4cc7-a2e4-82fa150b0b51

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalParamsProfile_one_eq
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_injective_on_exceptionalParams
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







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/



/-- Numerical number of exceptional *supports* with exactly one vertex
in G[2]. It is not the number of exceptional fibres. -/
theorem p2m_local_exceptionalSupportsProfile_one_card :
    (exceptionalSupportsProfile (G := G) 1).card =
      (twoTorsion : Finset G).card *
        ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by
  have hH : (0 : G) ∈ (twoTorsion : Finset G) :=
    (mem_twoTorsion 0).mpr (by simp)
  have hT : (0 : G) ∈ (threeTorsion : Finset G) :=
    (mem_threeTorsion 0).mpr (by simp)
  rw [exceptionalSupportsProfile_card_eq_params,
      exceptionalParamsProfile_one_eq]
  rw [Finset.product_eq_sprod, Finset.card_product]
  rw [Finset.product_eq_sprod, Finset.card_product]
  rw [Finset.card_erase_of_mem hH, Finset.card_erase_of_mem hT]


/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupportsProfile_one_card

