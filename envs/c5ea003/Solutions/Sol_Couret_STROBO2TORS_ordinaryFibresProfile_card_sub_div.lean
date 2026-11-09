-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibresProfile_card_sub_div
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:39.816052+00:00
-- url     : https://prove2.me/submissions/841f11d8-5afb-4c36-9612-ef9ffa7108cc

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_card_eq_mul
import Theorems.Thm_Couret_STROBO2TORS_tripleSupportsProfile_card
import Theorems.Thm_Couret_STROBO2TORS_tripleSupportsProfile_ordinary_exceptional
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]













theorem ordinary_exceptionalSupportsProfile_disjoint (j : ℕ) :
    Disjoint (ordinarySupportsProfile (G := G) j)
      (exceptionalSupportsProfile (G := G) j) := by
  apply Finset.disjoint_left.mpr
  intro S hO hE
  have h := (Finset.mem_filter.mp hO).2
  have he := (Finset.mem_filter.mp hE).2
  have hp := twoTorsion_card_pos (G := G)
  omega

/-- Key balance: profile supports = h * ordinary profile fibres +
exceptional supports. The exceptional term is a SUPPORT count, i.e. it
accounts automatically for the two H-orbits in every exceptional fibre. -/
theorem ordinaryProfile_card_balance (j : ℕ) :
    (tripleSupportsProfile (G := G) j).card =
      (twoTorsion : Finset G).card *
        (ordinaryFibresProfile (G := G) j).card +
        (exceptionalSupportsProfile (G := G) j).card := by
  rw [tripleSupportsProfile_ordinary_exceptional,
    Finset.card_union_of_disjoint (ordinary_exceptionalSupportsProfile_disjoint j),
    ordinarySupportsProfile_card_eq_mul]

/-- The ordinary-profile count is now reduced to a single concrete
exceptional-support stratum count, with no additional orbit ambiguity. -/
theorem ordinaryProfile_binomial_balance (j : ℕ) (hj : j ≤ 3) :
    (twoTorsion : Finset G).card *
        (ordinaryFibresProfile (G := G) j).card +
        (exceptionalSupportsProfile (G := G) j).card =
      ((twoTorsion : Finset G).card.choose j) *
        ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) := by
  rw [← ordinaryProfile_card_balance j]
  exact tripleSupportsProfile_card j hj

/-- An exact ordinary-fibre count in terms of the still-uncounted
exceptional support stratum. Dividing occurs ONLY after subtracting
the exceptional SUPPORT count, not the exceptional fibre count. -/
theorem p2m_local_ordinaryFibresProfile_card_sub_div (j : ℕ) (hj : j ≤ 3) :
    (ordinaryFibresProfile (G := G) j).card =
      (((twoTorsion : Finset G).card.choose j) *
        ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) -
        (exceptionalSupportsProfile (G := G) j).card) /
        (twoTorsion : Finset G).card := by
  have hbal := ordinaryProfile_binomial_balance (G := G) j hj
  calc
    (ordinaryFibresProfile (G := G) j).card =
        ((twoTorsion : Finset G).card *
          (ordinaryFibresProfile (G := G) j).card) /
          (twoTorsion : Finset G).card := by
            exact (Nat.mul_div_cancel_left _
              (twoTorsion_card_pos (G := G))).symm
    _ = (((twoTorsion : Finset G).card.choose j) *
          ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) -
          (exceptionalSupportsProfile (G := G) j).card) /
          (twoTorsion : Finset G).card := by
            rw [← hbal]
            congr 1
            omega





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
  @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (Nat.choose (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) j)
            (Nat.choose
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
          (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibresProfile_card_sub_div

