-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_histogram_semi_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:44:08.783687+00:00
-- url     : https://prove2.me/submissions/ab90e7a6-2d10-40b9-9f6c-7eda3f991ec5

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_histogram_formula
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_partition
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_filter_card_pos
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

































/-- Exact aggregation for every positive size. The ordinary term is still a
genuine finite-fibre count: this does NOT certify its binomial closed form. -/
theorem p2m_local_zeroFreeFullFibres_histogram_semi_numeric (k : ℕ) (hk : 0 < k) :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
    ((ordinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card +
    (if k = 2 * (twoTorsion : Finset G).card - 2 then
      3 * ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card else 0) +
    (if k = 2 * (twoTorsion : Finset G).card then
      ((doublingImages : Finset G).card - 3) *
        ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card else 0) := by
  rw [zeroFreeFullFibres_histogram_partition,
    zeroFreeOrdinaryFibres_filter_card_pos k hk,
    zeroFreeExceptionalFibres_histogram_formula]
  omega



/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (fun R => @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R) k)
          (fun a => instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a) k)
          (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (fun F =>
                @Eq.{1} Nat
                  (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F))
                  k)
              (fun a =>
                instDecidableEqNat
                  (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 a))
                  k)
              (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2)))
          (@ite.{1} Nat
            (@Eq.{1} Nat k
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (instDecidableEqNat k
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
                (@Couret.STROBO2TORS.threeSignPairs.{p2m_u_0} G inst inst_1 inst_2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@ite.{1} Nat
          (@Eq.{1} Nat k
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
          (instDecidableEqNat k
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.threeSignPairs.{p2m_u_0} G inst inst_1 inst_2)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_histogram_semi_numeric

