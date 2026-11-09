-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_top_size_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:38.091752+00:00
-- url     : https://prove2.me/submissions/ba235541-3074-4d4a-bdbc-0d550f169eec

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_nonempty_iff
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_top_filter_eq_exceptional
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]







/-- The absolute upper bound 2h is attained precisely when the
exceptional full-size stratum exists. These three inequalities are
independent of any special handling of coincident lower fibre sizes. -/
theorem p2m_local_zeroFreeFullFibres_top_size_nonempty_iff :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 2 * (twoTorsion : Finset G).card)).Nonempty ↔
      3 < (doublingImages : Finset G).card ∧
      1 < (twoTorsion : Finset G).card ∧
      1 < (threeTorsion : Finset G).card := by
  rw [zeroFreeFullFibres_top_filter_eq_exceptional]
  exact zeroFreeExceptionalFibres_full_nonempty_iff

end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  Iff
    (@Finset.Nonempty.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun R =>
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
        (fun a =>
          instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (And
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2)))
      (And
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_top_size_nonempty_iff

