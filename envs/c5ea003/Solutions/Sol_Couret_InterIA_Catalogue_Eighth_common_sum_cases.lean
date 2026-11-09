-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Eighth.common_sum_cases
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:47.233207+00:00
-- url     : https://prove2.me/submissions/a4aec198-fcd6-43dd-ae23-a1506d451af2

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
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm

theorem eight_steps_zero (n q : ℕ) (hn : n=8*q) : 8 • (q : ZMod n)=0 := by
  rw [nsmul_eq_mul,← Nat.cast_mul,← hn,ZMod.natCast_self]

theorem p2m_local_common_sum_cases (n q : ℕ) (hn : n=8*q) (c d : ZMod n)
    (hc : c=2 • (q : ZMod n) ∨ c=6 • (q : ZMod n))
    (hd : d=3 • (q : ZMod n) ∨ d=7 • (q : ZMod n)) :
    c+d=(q : ZMod n) ∨ c+d=5 • (q : ZMod n) := by
  have hz := eight_steps_zero n q hn
  rcases hc with rfl|rfl <;> rcases hd with rfl|rfl
  · right; abel
  · left
    calc 2 • (q : ZMod n)+7 • (q : ZMod n)=(q : ZMod n)+8 • (q : ZMod n) := by abel
         _=(q : ZMod n) := by rw [hz,add_zero]
  · left
    calc 6 • (q : ZMod n)+3 • (q : ZMod n)=(q : ZMod n)+8 • (q : ZMod n) := by abel
         _=(q : ZMod n) := by rw [hz,add_zero]
  · right
    calc 6 • (q : ZMod n)+7 • (q : ZMod n)=5 • (q : ZMod n)+8 • (q : ZMod n) := by abel
         _=5 • (q : ZMod n) := by rw [hz,add_zero]









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
          Or
            (@Eq.{1} (ZMod n)
              (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                (@instHAdd.{0} (ZMod n)
                  (@Distrib.toAdd.{0} (ZMod n)
                    (@instDistribOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                c d)
              (@Nat.cast.{0} (ZMod n)
                (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                    (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                q))
            (@Eq.{1} (ZMod n)
              (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                (@instHAdd.{0} (ZMod n)
                  (@Distrib.toAdd.{0} (ZMod n)
                    (@instDistribOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                c d)
              (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                (@instHSMul.{0, 0} Nat (ZMod n)
                  (@AddMonoid.toNSMul.{0} (ZMod n)
                    (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                        (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (@Nat.cast.{0} (ZMod n)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                      (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                  q))) := @_root_.Couret.InterIA.Catalogue.Eighth.p2m_local_common_sum_cases

