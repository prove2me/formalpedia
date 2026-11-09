-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrdinaryFibres_card_of_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:17.914043+00:00
-- url     : https://prove2.me/submissions/f4516b18-7bfb-4461-abbe-b2daa77e74f7

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nonemptyFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_nonempty_of_four
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_injective_on_nonemptyFullFibres
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

/-- If G[2] has at least four members, every ordinary complete fibre has a
nonempty zero-free restriction. This is stronger than a size formula:
there are no disappearing ordinary fibres. -/
theorem ordinaryNonemptyFibres_eq_ordinary_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (ordinaryNonemptyFibres : Finset (Finset (Finset G))) = ordinaryFibres := by
  unfold ordinaryNonemptyFibres
  ext F
  constructor
  · intro hF
    exact (Finset.mem_filter.mp hF).1
  · intro hF
    exact Finset.mem_filter.mpr
      ⟨hF, ordinaryFibres_nonempty_of_four hh F hF⟩

/-- Restriction preserves the number of ordinary fibres for h ≥ 4:
all restrictions are nonempty, and distinct original fibres remain distinct. -/
theorem p2m_local_zeroFreeOrdinaryFibres_card_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).card =
      (ordinaryFibres : Finset (Finset (Finset G))).card := by
  have hInj : Set.InjOn (withoutZero : Finset (Finset G) → Finset (Finset G))
      (ordinaryNonemptyFibres : Finset (Finset (Finset G))) := by
    intro F hF K hK heq
    have hF' : F ∈ (nonemptyFullFibres : Finset (Finset (Finset G))) := by
      rw [nonemptyFullFibres_eq_union]
      exact Finset.mem_union.mpr (Or.inl hF)
    have hK' : K ∈ (nonemptyFullFibres : Finset (Finset (Finset G))) := by
      rw [nonemptyFullFibres_eq_union]
      exact Finset.mem_union.mpr (Or.inl hK)
    exact withoutZero_injective_on_nonemptyFullFibres hF' hK' heq
  unfold zeroFreeOrdinaryFibres
  rw [Finset.card_image_iff.mpr hInj,
    ordinaryNonemptyFibres_eq_ordinary_of_four hh]











end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrdinaryFibres_card_of_four

