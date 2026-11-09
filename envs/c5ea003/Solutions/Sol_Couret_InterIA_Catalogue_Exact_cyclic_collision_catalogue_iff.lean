-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.cyclic_collision_catalogue_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:49.639486+00:00
-- url     : https://prove2.me/submissions/269abf88-2770-48e1-b207-9590b94732a8

import Aesop
import Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_ambient_reference_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_four_collision_shift_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_cyclic_collision_reference
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient











theorem p2m_local_cyclic_collision_catalogue_iff (n : ℕ) (hn : 4 ≤ n) (S T : Finset (ZMod n)) :
    FourCollision S T ↔
      ∃ m : ℕ, 0 < m ∧ n=2*m ∧ ∃ t : ZMod n, (t=0 ∨ t=m) ∧
        AmbientReferenceForm n S (T.image (fun z => z+t)) := by
  constructor
  · rintro ⟨hS,hT,hsq,hna⟩
    exact cyclic_collision_reference n hn S T hS hT hsq hna
  · rintro ⟨m,hm,hnm,t,ht,hform⟩
    have hc := ambient_reference_collision n S (T.image (fun z => z+t)) hform
    subst n
    have ht0 : t+t=0 := by
      rcases ht with rfl|rfl
      · simp
      · exact Couret.InterIA.L4.half_add_half m
    exact (four_collision_shift_iff S T t ht0).mp hc









end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    ∀ (S T : Finset.{0} (ZMod n)),
      Iff (@Couret.InterIA.Catalogue.Exact.FourCollision n S T)
        (@Exists.{1} Nat fun m =>
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
                            (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
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
                      T))))) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_cyclic_collision_catalogue_iff

