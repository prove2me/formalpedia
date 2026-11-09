-- Prove2me | solution 1 for Couret.InterIA.NormalForm.cyclic_four_L4_explicit
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:50:19.152311+00:00
-- url     : https://prove2.me/submissions/ef49796c-746d-41de-b312-338072ed095e

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
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres









/-- Expanded statement: two common points and two antipodal set differences. -/
theorem p2m_local_cyclic_four_L4_explicit (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    Even n ∧ ∃ t : ZMod n, (t=0 ∨ t=(n/2 : ℕ)) ∧
      (S ∩ T.image (fun x => x+t)).card=2 ∧
      ∃ a b : ZMod n,
        S \ T.image (fun x => x+t)={a,a+((n/2 : ℕ) : ZMod n)} ∧
        T.image (fun x => x+t) \ S={b,b+((n/2 : ℕ) : ZMod n)} := by
  simpa only [Normal,fibre] using cyclic_four_L4 n hn S T hS hT hsq hnaff

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
                    (And
                      (@Eq.{1} Nat
                        (@Finset.card.{0} (ZMod n)
                          (@Inter.inter.{0} (Finset.{0} (ZMod n)) (@Finset.instInter.{0} (ZMod n) (ZMod.decidableEq n))
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
                              T)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Exists.{1} (ZMod n) fun a =>
                        @Exists.{1} (ZMod n) fun b =>
                          And
                            (@Eq.{1} (Finset.{0} (ZMod n))
                              (@SDiff.sdiff.{0} (Finset.{0} (ZMod n))
                                (@Finset.instSDiff.{0} (ZMod n) (ZMod.decidableEq n)) S
                                (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
                                  (fun x =>
                                    @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                                      (@instHAdd.{0} (ZMod n)
                                        (@Distrib.toAdd.{0} (ZMod n)
                                          (@instDistribOfSemiring.{0} (ZMod n)
                                            (@CommSemiring.toSemiring.{0} (ZMod n)
                                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                                      x t)
                                  T))
                              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) a
                                (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                                  (@Finset.instSingleton.{0} (ZMod n))
                                  (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                                    (@instHAdd.{0} (ZMod n)
                                      (@Distrib.toAdd.{0} (ZMod n)
                                        (@instDistribOfSemiring.{0} (ZMod n)
                                          (@CommSemiring.toSemiring.{0} (ZMod n)
                                            (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                                    a
                                    (@Nat.cast.{0} (ZMod n)
                                      (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                          (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                            (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                                      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                            (@Eq.{1} (Finset.{0} (ZMod n))
                              (@SDiff.sdiff.{0} (Finset.{0} (ZMod n))
                                (@Finset.instSDiff.{0} (ZMod n) (ZMod.decidableEq n))
                                (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
                                  (fun x =>
                                    @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                                      (@instHAdd.{0} (ZMod n)
                                        (@Distrib.toAdd.{0} (ZMod n)
                                          (@instDistribOfSemiring.{0} (ZMod n)
                                            (@CommSemiring.toSemiring.{0} (ZMod n)
                                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                                      x t)
                                  T)
                                S)
                              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) b
                                (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                                  (@Finset.instSingleton.{0} (ZMod n))
                                  (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                                    (@instHAdd.{0} (ZMod n)
                                      (@Distrib.toAdd.{0} (ZMod n)
                                        (@instDistribOfSemiring.{0} (ZMod n)
                                          (@CommSemiring.toSemiring.{0} (ZMod n)
                                            (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                                    b
                                    (@Nat.cast.{0} (ZMod n)
                                      (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                          (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                            (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                                      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))) := @_root_.Couret.InterIA.NormalForm.p2m_local_cyclic_four_L4_explicit

