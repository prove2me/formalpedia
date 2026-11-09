-- Prove2me | solution 1 for Couret.InterIA.Fibres.even_four_fibre_ncard
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:53.407571+00:00
-- url     : https://prove2.me/submissions/b0ba0833-b7bc-40fb-ac32-86b27505ae8e

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
import Theorems.Thm_Couret_InterIA_Fibres_antipodal_free_four_ne_half_translate
import Theorems.Thm_Couret_InterIA_Fibres_two_simple_fibre_ncard
import Definitions.Def_Couret_StableFibreLift_7567a251f927

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.Projection







theorem p2m_local_even_four_fibre_ncard (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m))) (hS : S.card=4) :
    (cyclicFourFibre (2*m) S).ncard=1 ∨ (cyclicFourFibre (2*m) S).ncard=2 ∨
      (cyclicFourFibre (2*m) S).ncard=4 := by
  change (originalFibre m S).ncard=1 ∨ (originalFibre m S).ncard=2 ∨ (originalFibre m S).ncard=4
  rcases even_four_support_cases m hm S hS with hf|hs|⟨C,a,hC,hf,hd,hSe⟩
  · right; left
    change (cyclicFourFibre (2*m) S).ncard=2
    have he := antipodal_free_four_fibre_eq_pair m hm S hS hf
    change cyclicFourFibre (2*m) S=_ at he
    rw [he,Set.ncard_pair (antipodal_free_four_ne_half_translate m S hS hf)]
  · rcases stable_four_fibre_ncard m hm S hS hs with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [hSe]
    exact Or.inr (two_simple_fibre_ncard m hm C a hC hf hd)



end Couret.InterIA.Fibres

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (S :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
      @Eq.{1} Nat
          (@Finset.card.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            S)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Or
          (@Eq.{1} Nat
            (@Set.ncard.{0}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (Couret.InterIA.Fibres.cyclicFourFibre
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                S))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Or
            (@Eq.{1} Nat
              (@Set.ncard.{0}
                (Finset.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                (Couret.InterIA.Fibres.cyclicFourFibre
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                  S))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Eq.{1} Nat
              (@Set.ncard.{0}
                (Finset.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                (Couret.InterIA.Fibres.cyclicFourFibre
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                  S))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := @_root_.Couret.InterIA.Fibres.p2m_local_even_four_fibre_ncard

