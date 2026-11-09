-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrdinaryFibres_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:21:09.521438+00:00
-- url     : https://prove2.me/submissions/34d829fa-b948-4134-87e7-8a5bb95cdc78

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
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_injective_on_nonemptyFullFibres
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

























/-- The ordinary part can be counted at the level of genuine complete
fibres, provided that empty restrictions are excluded. -/
theorem p2m_local_zeroFreeOrdinaryFibres_filter_card (k : ℕ) :
    ((zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
    ((ordinaryNonemptyFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card := by
  unfold zeroFreeOrdinaryFibres
  rw [Finset.filter_image]
  apply Finset.card_image_iff.mpr
  intro F hF K hK heq
  have hf : F ∈ (nonemptyFullFibres : Finset (Finset (Finset G))) := by
    rw [nonemptyFullFibres_eq_union]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hF).1)
  have hk : K ∈ (nonemptyFullFibres : Finset (Finset (Finset G))) := by
    rw [nonemptyFullFibres_eq_union]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hK).1)
  exact withoutZero_injective_on_nonemptyFullFibres hf hk heq











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
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun R => @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R) k)
        (fun a => instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a) k)
        (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun F =>
          @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F)) k)
        (fun a =>
          instDecidableEqNat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 a)) k)
        (@Couret.STROBO2TORS.ordinaryNonemptyFibres.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrdinaryFibres_filter_card

