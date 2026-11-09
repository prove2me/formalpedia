-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinarySupportsProfile_card_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:03.915073+00:00
-- url     : https://prove2.me/submissions/380bee49-441c-4953-b26e-110ecdc96658

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_image
import Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_preimage
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]









/-- Uniform orbit size h gives the exact support-to-fibre factor. -/
theorem p2m_local_ordinarySupportsProfile_card_eq_mul (j : ℕ) :
    (ordinarySupportsProfile (G := G) j).card =
      (twoTorsion : Finset G).card *
        (ordinaryFibresProfile (G := G) j).card := by
  calc
    (ordinarySupportsProfile (G := G) j).card =
        ∑ F ∈ ((ordinarySupportsProfile (G := G) j).image squareFibre),
          ((ordinarySupportsProfile (G := G) j).filter
            (fun S => squareFibre S = F)).card :=
      Finset.card_eq_sum_card_image squareFibre (ordinarySupportsProfile (G := G) j)
    _ = ∑ F ∈ (ordinaryFibresProfile (G := G) j),
          F.card := by
        rw [ordinarySupportsProfile_image]
        apply Finset.sum_congr rfl
        intro F hF
        exact congrArg Finset.card (ordinarySupportsProfile_preimage j F hF)
    _ = ∑ _F ∈ (ordinaryFibresProfile (G := G) j),
          (twoTorsion : Finset G).card := by
        apply Finset.sum_congr rfl
        intro F hF
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hF).1).2
    _ = _ := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]; ac_rfl















/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (j : Nat),
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.ordinarySupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinarySupportsProfile_card_eq_mul

