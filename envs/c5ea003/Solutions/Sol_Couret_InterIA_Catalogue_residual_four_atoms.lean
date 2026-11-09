-- Prove2me | solution 1 for Couret.InterIA.Catalogue.residual_four_atoms
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:00.979459+00:00
-- url     : https://prove2.me/submissions/74831632-23e4-4c6a-abe1-aadc687fa6c3

import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
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
import Definitions.Def_Couret_L4Assembly_154a326d9c14

set_option autoImplicit false
namespace Couret.InterIA.Catalogue
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing
open Couret.InterIA.Projection











theorem p2m_local_residual_four_atoms (m : ℕ) (C : Finset (ZMod (2*m))) (hC : C.card=2)
    (a b : ZMod (2*m)) :
    ∃ c d : ZMod (2*m), c ≠ d ∧ C={c,d} ∧
      residual m C a b=A (projection m c)+A (projection m d)+A (projection m a)+A (projection m b) := by
  obtain ⟨c,d,hcd,rfl⟩ := Finset.card_eq_two.mp hC
  refine ⟨c,d,hcd,rfl,?_⟩
  rw [residual,Couret.InterIA.IntersectionTwo.indicator_pair c d hcd,map_add]
  change push m (AddMonoidAlgebra.single c 1)+push m (AddMonoidAlgebra.single d 1)+
    A (projection m a)+A (projection m b)=
    A (projection m c)+A (projection m d)+A (projection m a)+A (projection m b)
  rw [push_single,push_single]
  rfl









end Couret.InterIA.Catalogue

theorem solution : ∀ (m : Nat)
  (C :
    Finset.{0}
      (ZMod
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
  @Eq.{1} Nat
      (@Finset.card.{0}
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
        C)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    ∀
      (a b :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
      @Exists.{1}
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
        fun c =>
        @Exists.{1}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
          fun d =>
          And
            (@Ne.{1}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              c d)
            (And
              (@Eq.{1}
                (Finset.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                C
                (@Insert.insert.{0, 0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (Finset.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                  (@Finset.instInsert.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (ZMod.decidableEq
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                  c
                  (@Singleton.singleton.{0, 0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (Finset.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                    (@Finset.instSingleton.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                    d)))
              (@Eq.{1} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                (Couret.InterIA.Catalogue.residual m C a b)
                (@HAdd.hAdd.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@instHAdd.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@Distrib.toAdd.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@instDistribOfSemiring.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                        (@AddMonoidAlgebra.semiring.{0, 0} Int (ZMod m) Int.instSemiring
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                              (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))))
                  (@HAdd.hAdd.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@instHAdd.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@Distrib.toAdd.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                        (@instDistribOfSemiring.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                          (@AddMonoidAlgebra.semiring.{0, 0} Int (ZMod m) Int.instSemiring
                            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                                (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                  (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))))
                    (@HAdd.hAdd.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@instHAdd.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                        (@Distrib.toAdd.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                          (@instDistribOfSemiring.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                            (@AddMonoidAlgebra.semiring.{0, 0} Int (ZMod m) Int.instSemiring
                              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                                  (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                    (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))))
                      (@Couret.InterIA.Catalogue.A m
                        (@DFunLike.coe.{1, 1, 1}
                          (@RingHom.{0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod m)
                            (@Semiring.toNonAssocSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                            (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                              (@CommSemiring.toSemiring.{0} (ZMod m)
                                (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (fun x => ZMod m)
                          (@RingHom.instFunLike.{0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod m)
                            (@Semiring.toNonAssocSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                            (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                              (@CommSemiring.toSemiring.{0} (ZMod m)
                                (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                          (Couret.InterIA.Projection.projection m) c))
                      (@Couret.InterIA.Catalogue.A m
                        (@DFunLike.coe.{1, 1, 1}
                          (@RingHom.{0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod m)
                            (@Semiring.toNonAssocSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                            (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                              (@CommSemiring.toSemiring.{0} (ZMod m)
                                (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (fun x => ZMod m)
                          (@RingHom.instFunLike.{0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod m)
                            (@Semiring.toNonAssocSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                            (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                              (@CommSemiring.toSemiring.{0} (ZMod m)
                                (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                          (Couret.InterIA.Projection.projection m) d)))
                    (@Couret.InterIA.Catalogue.A m
                      (@DFunLike.coe.{1, 1, 1}
                        (@RingHom.{0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod m)
                          (@Semiring.toNonAssocSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommSemiring.toSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommRing.toCommSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (ZMod.commRing
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                          (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (fun x => ZMod m)
                        (@RingHom.instFunLike.{0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod m)
                          (@Semiring.toNonAssocSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommSemiring.toSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommRing.toCommSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (ZMod.commRing
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                          (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                        (Couret.InterIA.Projection.projection m) a)))
                  (@Couret.InterIA.Catalogue.A m
                    (@DFunLike.coe.{1, 1, 1}
                      (@RingHom.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod m)
                        (@Semiring.toNonAssocSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                        (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (fun x => ZMod m)
                      (@RingHom.instFunLike.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod m)
                        (@Semiring.toNonAssocSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                        (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                      (Couret.InterIA.Projection.projection m) b))))) := @_root_.Couret.InterIA.Catalogue.p2m_local_residual_four_atoms

