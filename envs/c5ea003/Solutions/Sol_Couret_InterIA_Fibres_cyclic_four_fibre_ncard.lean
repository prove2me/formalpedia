-- Prove2me | solution 1 for Couret.InterIA.Fibres.cyclic_four_fibre_ncard
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:15.611938+00:00
-- url     : https://prove2.me/submissions/252b0272-dc75-4a77-a000-7e3ecefc4d60

import Definitions.Def_Couret_UniversalFibre_5180566b07f2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_even_four_fibre_ncard
import Definitions.Def_Couret_StableFibreLift_7567a251f927

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.Projection









theorem p2m_local_cyclic_four_fibre_ncard (n : ℕ) (hn : 0 < n) (S : Finset (ZMod n)) (hS : S.card=4) :
    (cyclicFourFibre n S).ncard=1 ∨ (cyclicFourFibre n S).ncard=2 ∨ (cyclicFourFibre n S).ncard=4 := by
  rcases Nat.even_or_odd n with he|ho
  · obtain ⟨m,hm⟩ := he
    have hn2 : n=2*m := by omega
    clear hm
    subst n
    exact even_four_fibre_ncard m (by omega) S hS
  · exact Or.inl (by rw [odd_four_fibre_singleton n ho S hS,Set.ncard_singleton])

end Couret.InterIA.Fibres

theorem solution : ∀ (n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (S : Finset.{0} (ZMod n)),
      @Eq.{1} Nat (@Finset.card.{0} (ZMod n) S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Or
          (@Eq.{1} Nat (@Set.ncard.{0} (Finset.{0} (ZMod n)) (Couret.InterIA.Fibres.cyclicFourFibre n S))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Or
            (@Eq.{1} Nat (@Set.ncard.{0} (Finset.{0} (ZMod n)) (Couret.InterIA.Fibres.cyclicFourFibre n S))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Eq.{1} Nat (@Set.ncard.{0} (Finset.{0} (ZMod n)) (Couret.InterIA.Fibres.cyclicFourFibre n S))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := @_root_.Couret.InterIA.Fibres.p2m_local_cyclic_four_fibre_ncard

