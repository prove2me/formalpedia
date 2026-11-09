-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Eighth.reflection_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:46.678668+00:00
-- url     : https://prove2.me/submissions/7d711ef8-5fec-4e4b-a441-c49bff204eb4

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
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
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_common_sum_cases
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm

theorem eight_steps_zero (n q : ℕ) (hn : n=8*q) : 8 • (q : ZMod n)=0 := by
  rw [nsmul_eq_mul,← Nat.cast_mul,← hn,ZMod.natCast_self]





theorem p2m_local_reflection_image (n q : ℕ) (hn : n=8*q) (c d : ZMod n)
    (hc : c=2 • (q : ZMod n) ∨ c=6 • (q : ZMod n))
    (hd : d=3 • (q : ZMod n) ∨ d=7 • (q : ZMod n)) :
    ({c,d,0,4 • (q : ZMod n)} : Finset (ZMod n)).image (fun z => -z+c+d)=
      {c,d,(q : ZMod n),5 • (q : ZMod n)} := by
  have h8 := eight_steps_zero n q hn
  have h44 : 4 • (q : ZMod n)+4 • (q : ZMod n)=0 := by
    calc _=8 • (q : ZMod n) := by abel
         _=0 := h8
  have hneg : -(4 • (q : ZMod n) : ZMod n)=(4 • (q : ZMod n) : ZMod n) := by
    exact neg_eq_of_add_eq_zero_left h44
  have hci : -c+c+d=d := by abel
  have hdi : -d+c+d=c := by abel
  have hzi : -(0 : ZMod n)+c+d=c+d := by abel
  have hhi : -(4 • (q : ZMod n))+c+d=(c+d)+4 • (q : ZMod n) := by rw [hneg]; abel
  simp only [image_insert,image_singleton,hci,hdi,hzi,hhi]
  rcases common_sum_cases n q hn c d hc hd with hs|hs
  · have hh : (q : ZMod n)+4 • (q : ZMod n)=5 • (q : ZMod n) := by abel
    rw [hs,hh]
    ext z
    simp only [mem_insert,mem_singleton]
    tauto
  · have hh : 5 • (q : ZMod n)+4 • (q : ZMod n)=(q : ZMod n) := by
      calc _=(q : ZMod n)+8 • (q : ZMod n) := by abel
           _=(q : ZMod n) := by rw [h8,add_zero]
    rw [hs,hh]
    ext z
    simp only [mem_insert,mem_singleton]
    tauto





end Couret.InterIA.Catalogue.Eighth

theorem solution : ∀ (n q : Nat),
  @Eq.{1} Nat n
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) q) →
    ∀ (c d : ZMod n),
      Or
          (@Eq.{1} (ZMod n) c
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
                q)))
          (@Eq.{1} (ZMod n) c
            (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
              (@instHSMul.{0, 0} Nat (ZMod n)
                (@AddMonoid.toNSMul.{0} (ZMod n)
                  (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                      (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
              (@Nat.cast.{0} (ZMod n)
                (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                    (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                q))) →
        Or
            (@Eq.{1} (ZMod n) d
              (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                (@instHSMul.{0, 0} Nat (ZMod n)
                  (@AddMonoid.toNSMul.{0} (ZMod n)
                    (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                        (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.cast.{0} (ZMod n)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                      (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                  q)))
            (@Eq.{1} (ZMod n) d
              (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                (@instHSMul.{0, 0} Nat (ZMod n)
                  (@AddMonoid.toNSMul.{0} (ZMod n)
                    (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                        (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@Nat.cast.{0} (ZMod n)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                      (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                  q))) →
          @Eq.{1} (Finset.{0} (ZMod n))
            (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
              (fun z =>
                @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                  (@instHAdd.{0} (ZMod n)
                    (@Distrib.toAdd.{0} (ZMod n)
                      (@instDistribOfSemiring.{0} (ZMod n)
                        (@CommSemiring.toSemiring.{0} (ZMod n)
                          (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                  (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                    (@instHAdd.{0} (ZMod n)
                      (@Distrib.toAdd.{0} (ZMod n)
                        (@instDistribOfSemiring.{0} (ZMod n)
                          (@CommSemiring.toSemiring.{0} (ZMod n)
                            (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                    (@Neg.neg.{0} (ZMod n)
                      (@NegZeroClass.toNeg.{0} (ZMod n)
                        (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod n)
                          (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod n)
                            (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod n)
                              (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod n)
                                (@Ring.toAddCommGroup.{0} (ZMod n)
                                  (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))
                      z)
                    c)
                  d)
              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) c
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) d
                  (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                    (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                    (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (ZMod n)
                        (@MulZeroClass.toZero.{0} (ZMod n)
                          (@instMulZeroClassOfSemiring.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
                    (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                      (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                        (@instHSMul.{0, 0} Nat (ZMod n)
                          (@AddMonoid.toNSMul.{0} (ZMod n)
                            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                  (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.cast.{0} (ZMod n)
                          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                          q)))))))
            (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
              c
              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) d
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                  (@Nat.cast.{0} (ZMod n)
                    (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                        (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                    q)
                  (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                    (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                      (@instHSMul.{0, 0} Nat (ZMod n)
                        (@AddMonoid.toNSMul.{0} (ZMod n)
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.cast.{0} (ZMod n)
                        (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                            (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                        q)))))) := @_root_.Couret.InterIA.Catalogue.Eighth.p2m_local_reflection_image

