-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Parameters.two_pattern_parameter_separation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:33:08.629624+00:00
-- url     : https://prove2.me/submissions/1a4c3872-b857-4b19-a9c5-80d78f29b26d

import Definitions.Def_Couret_AffineParameterControls_321393084939
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
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_four_card_separations
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]





theorem p2m_local_two_pattern_parameter_separation (n q : ℕ) (hn : n=4*q) (x : ZMod n)
    (hc : ({0,(q : ZMod n),x,x+2 • (q : ZMod n)} : Finset (ZMod n)).card=4) :
    x ∉ ({0,(q : ZMod n),2 • (q : ZMod n),3 • (q : ZMod n)} : Finset (ZMod n)) := by
  have h4 : 4 • (q : ZMod n)=0 := by
    rw [nsmul_eq_mul,← Nat.cast_mul,← hn,ZMod.natCast_self]
  have hs := four_card_separations (0 : ZMod n) (q : ZMod n) x (x+2 • (q : ZMod n)) hc
  intro hx
  simp only [mem_insert,mem_singleton] at hx
  rcases hx with hx|hx|hx|hx
  · exact hs.1 hx
  · exact hs.2.1 hx
  · apply hs.2.2.1
    calc x+2 • (q : ZMod n)=4 • (q : ZMod n) := by rw [hx]; abel
         _=0 := h4
  · apply hs.2.2.2
    calc x+2 • (q : ZMod n)=(q : ZMod n)+4 • (q : ZMod n) := by rw [hx]; abel
         _=(q : ZMod n) := by rw [h4,add_zero]







end Couret.InterIA.Catalogue.Parameters

theorem solution : ∀ (n q : Nat),
  @Eq.{1} Nat n
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) →
    ∀ (x : ZMod n),
      @Eq.{1} Nat
          (@Finset.card.{0} (ZMod n)
            (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
              (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                (@Zero.toOfNat0.{0} (ZMod n)
                  (@MulZeroClass.toZero.{0} (ZMod n)
                    (@instMulZeroClassOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                (@Nat.cast.{0} (ZMod n)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                      (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                  q)
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) x
                  (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                    (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                      (@instHAdd.{0} (ZMod n)
                        (@Distrib.toAdd.{0} (ZMod n)
                          (@instDistribOfSemiring.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                      x
                      (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                        (@instHSMul.{0, 0} Nat (ZMod n)
                          (@AddMonoid.toNSMul.{0} (ZMod n)
                            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                  (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.cast.{0} (ZMod n)
                          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                          q))))))))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Not
          (@Membership.mem.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (ZMod n)) (ZMod n) (@Finset.instSetLike.{0} (ZMod n)))
            (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
              (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                (@Zero.toOfNat0.{0} (ZMod n)
                  (@MulZeroClass.toZero.{0} (ZMod n)
                    (@instMulZeroClassOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                (@Nat.cast.{0} (ZMod n)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                      (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                  q)
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                  (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                    (@instHSMul.{0, 0} Nat (ZMod n)
                      (@AddMonoid.toNSMul.{0} (ZMod n)
                        (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                            (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.cast.{0} (ZMod n)
                      (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                      q))
                  (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                    (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                      (@instHSMul.{0, 0} Nat (ZMod n)
                        (@AddMonoid.toNSMul.{0} (ZMod n)
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.cast.{0} (ZMod n)
                        (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                            (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                        q))))))
            x) := @_root_.Couret.InterIA.Catalogue.Parameters.p2m_local_two_pattern_parameter_separation

