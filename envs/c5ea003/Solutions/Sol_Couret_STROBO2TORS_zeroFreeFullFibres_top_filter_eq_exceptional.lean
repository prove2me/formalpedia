-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_top_filter_eq_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:03.778698+00:00
-- url     : https://prove2.me/submissions/586d38e0-7a07-44bd-a285-1455cb6ff2a5

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]





/-- The top-size fibres (size 2h) are exactly the exceptional ones:
ordinary fibres have at most h elements, whereas h is positive. -/
theorem p2m_local_zeroFreeFullFibres_top_filter_eq_exceptional :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 2 * (twoTorsion : Finset G).card)) =
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 2 * (twoTorsion : Finset G).card)) := by
  ext R
  constructor
  · intro hR
    obtain ⟨hFull, hSize⟩ := Finset.mem_filter.mp hR
    rw [zeroFreeFullFibres_eq_union] at hFull
    rcases Finset.mem_union.mp hFull with hOrd | hExc
    · have hBound := zeroFreeOrdinaryFibres_card_le_twoTorsion R hOrd
      have hPos := twoTorsion_card_pos (G := G)
      omega
    · exact Finset.mem_filter.mpr ⟨hExc, hSize⟩
  · intro hR
    obtain ⟨hExc, hSize⟩ := Finset.mem_filter.mp hR
    apply Finset.mem_filter.mpr
    constructor
    · rw [zeroFreeFullFibres_eq_union]
      exact Finset.mem_union.mpr (Or.inr hExc)
    · exact hSize



end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
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
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2))
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
      (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_top_filter_eq_exceptional

