-- Prove2me | solution 1 for Couret.STROBO2TORS.directed_nontranslation_degree_sum_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:54.995001+00:00
-- url     : https://prove2.me/submissions/4eace2b6-750a-4633-b33e-52aac98f49ac

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]















/-- Fully numerical DIRECTED partner incidence count.
Obtaining an unordered-pair count requires a separate symmetry/2-to-1 lemma. -/
theorem p2m_local_directed_nontranslation_degree_sum_numeric :
    (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) =
      (Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1)) *
        (twoTorsion : Finset G).card := by
  rw [directed_nontranslation_degree_sum, exceptionalSupports_card]

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.sum.{p2m_u_0, 0} (Finset.{p2m_u_0} G) Nat Nat.instAddCommMonoid
      (@Couret.STROBO2TORS.tripleSupports.{p2m_u_0} G inst_2) fun S =>
      @Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nontranslatedNeighbours.{p2m_u_0} G inst inst_1 inst_2 S))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_directed_nontranslation_degree_sum_numeric

