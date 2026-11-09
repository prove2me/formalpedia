-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrdinaryFibres_filter_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:30:06.483344+00:00
-- url     : https://prove2.me/submissions/c6202edd-a22b-438b-9983-8e28dbd8df34

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_filter_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]



























/-- A positive restriction size automatically rules out empty ordinary fibres.
This lets the ordinary histogram be counted on the original complete fibres. -/
theorem p2m_local_zeroFreeOrdinaryFibres_filter_card_pos (k : ℕ) (hk : 0 < k) :
    ((zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
    ((ordinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card := by
  rw [zeroFreeOrdinaryFibres_filter_card]
  congr 1
  ext F
  simp only [ordinaryNonemptyFibres, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · rintro ⟨hF, hK⟩
    exact ⟨⟨hF, Finset.card_pos.mp (by omega)⟩, hK⟩









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
          (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (fun F =>
            @Eq.{1} Nat
              (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F))
              k)
          (fun a =>
            instDecidableEqNat
              (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 a))
              k)
          (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrdinaryFibres_filter_card_pos

