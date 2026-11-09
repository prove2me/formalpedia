-- Prove2me | solution 1 for Couret.InterIA.NormalForm.cyclic_four_L4
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:45.948149+00:00
-- url     : https://prove2.me/submissions/2a818ef7-a6b4-41d3-8b45-9d6bf492e884

import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Theorems.Thm_Couret_InterIA_NormalForm_translation_is_affine
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres







/-- L4 for all cyclic orders n>=4; no parity assumption is supplied by the caller. -/
theorem p2m_local_cyclic_four_L4 (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    Even n ∧ ∃ t : ZMod n, (t=0 ∨ t=(n/2 : ℕ)) ∧
      Normal ((n/2 : ℕ) : ZMod n) S (T.image (fun x => x+t)) := by
  have heven : Even n := by
    by_contra hne
    have hodd : Odd n := Nat.not_even_iff_odd.mp hne
    have he := odd_cyclic_square_injective n hodd S T hsq
    exact hnaff (translation_is_affine S T 0 (by simpa using he))
  refine ⟨heven,?_⟩
  obtain ⟨m,hm⟩ := heven
  have hnm : n=2*m := by omega
  clear hm
  subst n
  have hmp : 0 < m := by omega
  have hdiv : 2*m/2=m := by omega
  simpa only [hdiv] using even_cyclic_L4 m hmp S T hS hT hsq hnaff



end Couret.InterIA.NormalForm

theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    ∀ (S T : Finset.{0} (ZMod n)),
      @Eq.{1} Nat (@Finset.card.{0} (ZMod n) S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Eq.{1} Nat (@Finset.card.{0} (ZMod n) T) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          (∀ (z : ZMod n),
              @Eq.{1} Nat
                (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
                  (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                  (ZMod.decidableEq n) S z)
                (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
                  (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                  (ZMod.decidableEq n) T z)) →
            Not (@Couret.InterIA.NormalForm.AffineEquivalent n S T) →
              And (@Even.{0} Nat instAddNat n)
                (@Exists.{1} (ZMod n) fun t =>
                  And
                    (Or
                      (@Eq.{1} (ZMod n) t
                        (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (ZMod n)
                            (@MulZeroClass.toZero.{0} (ZMod n)
                              (@instMulZeroClassOfSemiring.{0} (ZMod n)
                                (@CommSemiring.toSemiring.{0} (ZMod n)
                                  (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))))
                      (@Eq.{1} (ZMod n) t
                        (@Nat.cast.{0} (ZMod n)
                          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@Couret.InterIA.NormalForm.Normal.{0} (ZMod n)
                      (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                      (ZMod.decidableEq n)
                      (@Nat.cast.{0} (ZMod n)
                        (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                            (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      S
                      (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
                        (fun x =>
                          @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                            (@instHAdd.{0} (ZMod n)
                              (@Distrib.toAdd.{0} (ZMod n)
                                (@instDistribOfSemiring.{0} (ZMod n)
                                  (@CommSemiring.toSemiring.{0} (ZMod n)
                                    (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                            x t)
                        T))) := @_root_.Couret.InterIA.NormalForm.p2m_local_cyclic_four_L4

