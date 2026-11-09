-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Ambient.cyclic_collision_reference
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:32:10.614501+00:00
-- url     : https://prove2.me/submissions/12a93285-5431-4d12-8875-f6b9220d8cde

import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_nonaffine_collision_two_form
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_cyclic_collision_eight_divides
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_normalised_patterns_reference_form
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive Couret.InterIA.Catalogue.Parameters
open Couret.InterIA.Catalogue.AffineTransport Couret.InterIA.Parity





theorem controlled_form_reference (m : ℕ) (S T : Finset (ZMod (2*m)))
    (h : TwoControlledForm m S T) (hna : ¬ AffineEquivalent S T) :
    AmbientReferenceForm (2*m) S T := by
  obtain ⟨q,hq,hn,heven,u,v,x,hx,hS,hT⟩ := h
  exact normalised_patterns_reference_form (2*m) q hn hq S T u v x hx hS hT hna

/-- Starts with the actual collision and retains its possible unilateral half-turn. -/
theorem nonaffine_collision_reference (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hna : ¬ AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      AmbientReferenceForm (2*m) S (T.image (fun z => z+t)) := by
  obtain ⟨t,ht,hform⟩ := Couret.InterIA.Catalogue.Eighth.nonaffine_collision_two_form m hm S T hS hT hsq hna
  refine ⟨t,ht,controlled_form_reference m S (T.image (fun z => z+t)) hform ?_⟩
  intro he
  exact hna ((unilateral_translation_equivalent_iff S T t).mp he)

/-- Arbitrary cyclic modulus, using the received necessity of eight-divisibility. -/
theorem p2m_local_cyclic_collision_reference (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hna : ¬ AffineEquivalent S T) :
    ∃ m : ℕ, 0 < m ∧ n=2*m ∧ ∃ t : ZMod n, (t=0 ∨ t=m) ∧
      AmbientReferenceForm n S (T.image (fun z => z+t)) := by
  obtain ⟨k,hk⟩ := Couret.InterIA.Catalogue.Lifts.cyclic_collision_eight_divides n hn S T hS hT hsq hna
  have hnm : n=2*(4*k) := by omega
  have hm : 0 < 4*k := by omega
  clear hk
  subst n
  obtain ⟨t,ht,hform⟩ := nonaffine_collision_reference (4*k) hm S T hS hT hsq hna
  exact ⟨4*k,hm,rfl,t,ht,hform⟩

end Couret.InterIA.Catalogue.Quarter.Ambient

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
              @Exists.{1} Nat fun m =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
                  (And
                    (@Eq.{1} Nat n
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
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
                                  (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                    (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                              m)))
                        (Couret.InterIA.Catalogue.Quarter.Ambient.AmbientReferenceForm n S
                          (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
                            (fun z =>
                              @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                                (@instHAdd.{0} (ZMod n)
                                  (@Distrib.toAdd.{0} (ZMod n)
                                    (@instDistribOfSemiring.{0} (ZMod n)
                                      (@CommSemiring.toSemiring.{0} (ZMod n)
                                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                                z t)
                            T)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Ambient.p2m_local_cyclic_collision_reference

