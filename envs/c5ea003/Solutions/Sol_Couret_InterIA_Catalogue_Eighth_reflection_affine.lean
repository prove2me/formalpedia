-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Eighth.reflection_affine
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:50.602241+00:00
-- url     : https://prove2.me/submissions/f0ef1954-0d55-4dfd-8b40-014188425519

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
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_reflection_image
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm











theorem p2m_local_reflection_affine (n q : ℕ) (hn : n=8*q) (c d : ZMod n)
    (hc : c=2 • (q : ZMod n) ∨ c=6 • (q : ZMod n))
    (hd : d=3 • (q : ZMod n) ∨ d=7 • (q : ZMod n)) :
    AffineEquivalent ({c,d,0,4 • (q : ZMod n)} : Finset (ZMod n))
      {c,d,(q : ZMod n),5 • (q : ZMod n)} := by
  let U : (ZMod n)ˣ := ⟨-1,-1,by ring,by ring⟩
  refine ⟨U,c+d,?_⟩
  change ({c,d,0,4 • (q : ZMod n)} : Finset (ZMod n)).image
    (fun z => (-1 : ZMod n)*z+(c+d))={c,d,(q : ZMod n),5 • (q : ZMod n)}
  simpa only [neg_one_mul,add_assoc] using reflection_image n q hn c d hc hd

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
          @Couret.InterIA.NormalForm.AffineEquivalent n
            (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
              c
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
                        q))))))
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
                        q)))))) := @_root_.Couret.InterIA.Catalogue.Eighth.p2m_local_reflection_affine

