-- Prove2me | solution 1 for Couret.InterIA.QuotientBridge.quotient_unit_lift
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:50:09.559783+00:00
-- url     : https://prove2.me/submissions/b0dec588-1b84-4fd0-8510-9426375fc7b2

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo Couret.InterIA.Projection











section Moment
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







end Moment















/-- Reuse mathlib's general unit lifting; this alone does not classify seeds. -/
theorem p2m_local_quotient_unit_lift (m : ℕ) (hm : 0 < m) (u : (ZMod m)ˣ) :
    ∃ v : (ZMod (2*m))ˣ, ZMod.unitsMap (dvd_mul_left m 2) v = u := by
  letI : NeZero (2*m) := ⟨by omega⟩
  exact ZMod.unitsMap_surjective (dvd_mul_left m 2) u

end Couret.InterIA.QuotientBridge

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (u :
        @Units.{0} (ZMod m)
          (@Semiring.toMonoid.{0} (ZMod m)
            (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m))))),
      @Exists.{1}
        (@Units.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
          (@Semiring.toMonoid.{0}
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
        fun v =>
        @Eq.{1}
          (@Units.{0} (ZMod m)
            (@Semiring.toMonoid.{0} (ZMod m)
              (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0}
              (@Units.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                    (@instHMul.{0} Nat
                      (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@Semiring.toMonoid.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@CommSemiring.toSemiring.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommRing.toCommSemiring.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
              (@Units.{0} (ZMod m)
                (@Semiring.toMonoid.{0} (ZMod m)
                  (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
              (@MulOneClass.toMulOne.{0}
                (@Units.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Semiring.toMonoid.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommSemiring.toSemiring.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@CommRing.toCommSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
                (@Units.instMulOneClass.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Semiring.toMonoid.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommSemiring.toSemiring.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@CommRing.toCommSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))))
              (@MulOneClass.toMulOne.{0}
                (@Units.{0} (ZMod m)
                  (@Semiring.toMonoid.{0} (ZMod m)
                    (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                (@Units.instMulOneClass.{0} (ZMod m)
                  (@Semiring.toMonoid.{0} (ZMod m)
                    (@CommSemiring.toSemiring.{0} (ZMod m)
                      (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
            (@Units.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                  (@instHMul.{0} Nat
                    (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@Semiring.toMonoid.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                    (@instHMul.{0} Nat
                      (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@CommSemiring.toSemiring.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@CommRing.toCommSemiring.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
            (fun x =>
              @Units.{0} (ZMod m)
                (@Semiring.toMonoid.{0} (ZMod m)
                  (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
            (@MonoidHom.instFunLike.{0, 0}
              (@Units.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                    (@instHMul.{0} Nat
                      (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@Semiring.toMonoid.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@CommSemiring.toSemiring.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommRing.toCommSemiring.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
              (@Units.{0} (ZMod m)
                (@Semiring.toMonoid.{0} (ZMod m)
                  (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
              (@MulOneClass.toMulOne.{0}
                (@Units.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Semiring.toMonoid.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommSemiring.toSemiring.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@CommRing.toCommSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
                (@Units.instMulOneClass.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                      (@instHMul.{0} Nat
                        (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Semiring.toMonoid.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                        (@instHMul.{0} Nat
                          (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommSemiring.toSemiring.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                          (@instHMul.{0} Nat
                            (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@CommRing.toCommSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                            (@instHMul.{0} Nat
                              (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))))
              (@MulOneClass.toMulOne.{0}
                (@Units.{0} (ZMod m)
                  (@Semiring.toMonoid.{0} (ZMod m)
                    (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                (@Units.instMulOneClass.{0} (ZMod m)
                  (@Semiring.toMonoid.{0} (ZMod m)
                    (@CommSemiring.toSemiring.{0} (ZMod m)
                      (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
            (@ZMod.unitsMap m
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                (@instHMul.{0} Nat
                  (@CommMagma.toMul.{0} Nat (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
              (@dvd_mul_left.{0} Nat Nat.instCommSemigroup m
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            v)
          u := @_root_.Couret.InterIA.QuotientBridge.p2m_local_quotient_unit_lift

