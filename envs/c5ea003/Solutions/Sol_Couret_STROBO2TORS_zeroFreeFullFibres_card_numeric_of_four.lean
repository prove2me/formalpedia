-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_card_numeric_of_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:11.013385+00:00
-- url     : https://prove2.me/submissions/a6440787-eb12-4980-8016-863f4bdf698d

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_weighted_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_of_four
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]











/-- For h ≥ 4, the number of observed nonempty zero-free fibres is
choose(n,3)/h - E, where E is the actual exceptional-fibre count. -/
theorem zeroFreeFullFibres_card_sub_exception_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).card =
      (Fintype.card G).choose 3 / (twoTorsion : Finset G).card -
        (exceptionalFibres : Finset (Finset (Finset G))).card := by
  have hWeighted :
      (Fintype.card G).choose 3 / (twoTorsion : Finset G).card =
        (ordinaryFibres : Finset (Finset (Finset G))).card +
          2 * (exceptionalFibres : Finset (Finset (Finset G))).card := by
    rw [tripleSupports_weighted_card]
    exact Nat.mul_div_cancel_left _ (twoTorsion_card_pos (G := G))
  rw [zeroFreeFullFibres_card_of_four hh]
  omega

/-- Explicit full-fibre count with zero forbidden, valid for every finite
abelian G with |G[2]| ≥ 4. Not yet the per-size binomial histogram. -/
theorem p2m_local_zeroFreeFullFibres_card_numeric_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).card =
      (Fintype.card G).choose 3 / (twoTorsion : Finset G).card -
        ((Fintype.card G / (twoTorsion : Finset G).card) *
          ((twoTorsion : Finset G).card - 1) *
          (((threeTorsion : Finset G).card - 1) / 2)) := by
  rw [zeroFreeFullFibres_card_sub_exception_of_four hh,
    exceptionalFibres_card_numeric]

end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (Nat.choose (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@Fintype.card.{p2m_u_0} G inst_2)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_card_numeric_of_four

