-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_histogram_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:53.831931+00:00
-- url     : https://prove2.me/submissions/74cef87a-7884-45a8-b4f0-7b11de330849

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]



































/-- Empty ordinary restrictions are deliberately excluded from the histogram.
In particular, the displayed histogram has no size-zero entry. -/
theorem p2m_local_zeroFreeFullFibres_histogram_zero :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 0)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  ext R
  constructor
  · intro hR
    obtain ⟨hF, h0⟩ := Finset.mem_filter.mp hR
    obtain ⟨F, hF', hFR⟩ := Finset.mem_image.mp hF
    have hne : (withoutZero F).Nonempty := (Finset.mem_filter.mp hF').2
    have hp : 0 < R.card := by
      rw [← hFR]
      exact Finset.card_pos.mpr hne
    omega
  · intro h
    simp at h

/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun R =>
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (fun a =>
          instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_histogram_zero

