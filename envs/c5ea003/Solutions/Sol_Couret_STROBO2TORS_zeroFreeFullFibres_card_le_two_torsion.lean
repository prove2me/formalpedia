-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_card_le_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:06.37124+00:00
-- url     : https://prove2.me/submissions/341ac61a-be68-49ae-b130-d71f47391da3

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_only_two_sizes
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]



/-- No nonempty zero-free triple-square fibre has more than twice the
number of two-torsion elements. This is a universal upper bound,
not yet an exhaustive case-by-case sharp maximum formula. -/
theorem p2m_local_zeroFreeFullFibres_card_le_two_torsion
    (R : Finset (Finset G))
    (hR : R ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    R.card ≤ 2 * (twoTorsion : Finset G).card := by
  rw [zeroFreeFullFibres_eq_union] at hR
  rcases Finset.mem_union.mp hR with hOrd | hExc
  · have hb := zeroFreeOrdinaryFibres_card_le_twoTorsion R hOrd
    omega
  · rcases zeroFreeExceptionalFibres_only_two_sizes R hExc with hs | hs
    · omega
    · omega





end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (R : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) R →
    @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_card_le_two_torsion

