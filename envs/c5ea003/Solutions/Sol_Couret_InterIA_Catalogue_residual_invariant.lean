-- Prove2me | solution 1 for Couret.InterIA.Catalogue.residual_invariant
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:26.969632+00:00
-- url     : https://prove2.me/submissions/814a0599-a18f-4456-aec9-5e3ba18ad56b

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





theorem atom_product {m : ℕ} (x y : ZMod m) : A x*A y=A (x+y) := by
  simp [A,AddMonoidAlgebra.single_mul_single]



theorem p2m_local_residual_invariant (m : ℕ) (hm : 0 < m) (C : Finset (ZMod (2*m)))
    (a b : ZMod (2*m))
    (he : (A (projection m a)-A (projection m b))*residual m C a b=0) :
    residual m C a b=A (projection m (b-a))*residual m C a b := by
  have hp := congrArg (fun f : AddMonoidAlgebra ℤ (ZMod m) => A (-projection m a)*f) he
  change A (-projection m a)*((A (projection m a)-A (projection m b))*residual m C a b)=
    A (-projection m a)*0 at hp
  rw [mul_zero] at hp
  have heq : A (-projection m a)*((A (projection m a)-A (projection m b))*residual m C a b)=
      residual m C a b-A (projection m (b-a))*residual m C a b := by
    rw [← mul_assoc,mul_sub,sub_mul,atom_product,atom_product]
    have hz : A (0 : ZMod m)=(1 : AddMonoidAlgebra ℤ (ZMod m)) := by
      simp [A,AddMonoidAlgebra.one_def]
    have hi : -projection m a+projection m b=projection m (b-a) := by rw [map_sub]; abel
    rw [neg_add_cancel,hz,one_mul,hi]
  rw [heq] at hp
  exact sub_eq_zero.mp hp











end Couret.InterIA.Catalogue

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (C :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
      (a b :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
      @Eq.{1} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
          (@HMul.hMul.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
            (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
            (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
            (@instHMul.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@AddMonoidAlgebra.instMul.{0, 0} Int (ZMod m) Int.instSemiring
                (@Distrib.toAdd.{0} (ZMod m)
                  (@instDistribOfSemiring.{0} (ZMod m)
                    (@CommSemiring.toSemiring.{0} (ZMod m)
                      (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
            (@HSub.hSub.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@instHSub.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                (@SubNegMonoid.toSub.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@AddGroup.toSubNegMonoid.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@AddGroupWithOne.toAddGroup.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@Ring.toAddGroupWithOne.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                        (@AddMonoidAlgebra.ring.{0, 0} Int (ZMod m) Int.instRing
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                              (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))))))
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
                  (Couret.InterIA.Projection.projection m) a))
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
                  (Couret.InterIA.Projection.projection m) b)))
            (Couret.InterIA.Catalogue.residual m C a b))
          (@OfNat.ofNat.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring) (nat_lit 0)
            (@Zero.toOfNat0.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@MulZeroClass.toZero.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                (@instMulZeroClassOfSemiring.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@AddMonoidAlgebra.semiring.{0, 0} Int (ZMod m) Int.instSemiring
                    (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                        (@Ring.toAddGroupWithOne.{0} (ZMod m)
                          (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))))) →
        @Eq.{1} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring) (Couret.InterIA.Catalogue.residual m C a b)
          (@HMul.hMul.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
            (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
            (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
            (@instHMul.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@AddMonoidAlgebra.instMul.{0, 0} Int (ZMod m) Int.instSemiring
                (@Distrib.toAdd.{0} (ZMod m)
                  (@instDistribOfSemiring.{0} (ZMod m)
                    (@CommSemiring.toSemiring.{0} (ZMod m)
                      (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
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
                    (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
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
                    (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                (Couret.InterIA.Projection.projection m)
                (@HSub.hSub.{0, 0, 0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@instHSub.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@SubNegMonoid.toSub.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@AddGroup.toSubNegMonoid.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (@AddGroupWithOne.toAddGroup.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))))
                  b a)))
            (Couret.InterIA.Catalogue.residual m C a b)) := @_root_.Couret.InterIA.Catalogue.p2m_local_residual_invariant

