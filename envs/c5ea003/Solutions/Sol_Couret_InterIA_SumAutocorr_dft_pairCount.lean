-- Prove2me | solution 1 for Couret.InterIA.SumAutocorr.dft_pairCount
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:39.419565+00:00
-- url     : https://prove2.me/submissions/e4c132e6-1b87-40f2-8d28-98fbae0017a9

import Definitions.Def_Couret_SumAutocorr_074e6f9ba1f0
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
namespace Couret.InterIA.SumAutocorr
open Finset Couret.InterIA.Parity

variable {n : ℕ} [NeZero n]











theorem p2m_local_dft_pairCount (S T : Finset (ZMod n))
    (op : ZMod n → ZMod n → ZMod n) (k : ZMod n) :
    ZMod.dft (fun z => (pairCount S T op z : ℂ)) k =
      ∑ a ∈ S, ∑ b ∈ T, ZMod.stdAddChar (-(op a b*k)) := by
  classical
  simp only [ZMod.dft_apply,smul_eq_mul,pairCount,Nat.cast_sum,apply_ite,
    Nat.cast_one,Nat.cast_zero,Finset.mul_sum,mul_one,mul_zero]
  calc
    _ = ∑ a ∈ S, ∑ z : ZMod n, ∑ b ∈ T,
        (if op a b=z then ZMod.stdAddChar (-(z*k)) else 0) := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ b ∈ T, ∑ z : ZMod n,
        (if op a b=z then ZMod.stdAddChar (-(z*k)) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by simp











end Couret.InterIA.SumAutocorr

theorem solution : ∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] (S T : Finset.{0} (ZMod n))
  (op : ZMod n → ZMod n → ZMod n) (k : ZMod n),
  @Eq.{1} Complex
    (@DFunLike.coe.{1, 1, 1}
      (@LinearEquiv.{0, 0, 0, 0} Complex Complex Complex.instSemiring Complex.instSemiring
        (@RingHom.id.{0} Complex (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
        (@RingHom.id.{0} Complex (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
        (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
        (ZMod n → Complex) (ZMod n → Complex)
        (@Pi.addCommMonoid.{0, 0} (ZMod n) (fun a => Complex) fun i =>
          @AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
        (@Pi.addCommMonoid.{0, 0} (ZMod n) (fun a => Complex) fun i =>
          @AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
        (@Pi.Function.module.{0, 0, 0} (ZMod n) Complex Complex Complex.instSemiring
          (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
          (@Semiring.toModule.{0} Complex Complex.instSemiring))
        (@Pi.Function.module.{0, 0, 0} (ZMod n) Complex Complex Complex.instSemiring
          (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
          (@Semiring.toModule.{0} Complex Complex.instSemiring)))
      (ZMod n → Complex) (fun x => ZMod n → Complex)
      (@EquivLike.toFunLike.{1, 1, 1}
        (@LinearEquiv.{0, 0, 0, 0} Complex Complex Complex.instSemiring Complex.instSemiring
          (@RingHom.id.{0} Complex (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
          (@RingHom.id.{0} Complex (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
          (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
          (ZMod n → Complex) (ZMod n → Complex)
          (@Pi.addCommMonoid.{0, 0} (ZMod n) (fun a => Complex) fun i =>
            @AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
          (@Pi.addCommMonoid.{0, 0} (ZMod n) (fun a => Complex) fun i =>
            @AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
          (@Pi.Function.module.{0, 0, 0} (ZMod n) Complex Complex Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
            (@Semiring.toModule.{0} Complex Complex.instSemiring))
          (@Pi.Function.module.{0, 0, 0} (ZMod n) Complex Complex Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
            (@Semiring.toModule.{0} Complex Complex.instSemiring)))
        (ZMod n → Complex) (ZMod n → Complex)
        (@DFinsupp.instEquivLikeLinearEquiv.{0, 0, 0, 0} Complex Complex Complex.instSemiring Complex.instSemiring
          (@RingHom.id.{0} Complex (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
          (@RingHom.id.{0} Complex (@Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiring))
          (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
          (ZMod n → Complex) (ZMod n → Complex)
          (@Pi.addCommMonoid.{0, 0} (ZMod n) (fun a => Complex) fun i =>
            @AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
          (@Pi.addCommMonoid.{0, 0} (ZMod n) (fun a => Complex) fun i =>
            @AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
          (@Pi.Function.module.{0, 0, 0} (ZMod n) Complex Complex Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
            (@Semiring.toModule.{0} Complex Complex.instSemiring))
          (@Pi.Function.module.{0, 0, 0} (ZMod n) Complex Complex Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
            (@Semiring.toModule.{0} Complex Complex.instSemiring))))
      (@ZMod.dft.{0} n inst Complex Complex.addCommGroup (@Semiring.toModule.{0} Complex Complex.instSemiring))
      (fun z => @Nat.cast.{0} Complex Complex.instNatCast (@Couret.InterIA.SumAutocorr.pairCount n S T op z)) k)
    (@Finset.sum.{0, 0} (ZMod n) Complex
      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                  (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField)))))))
      S fun a =>
      @Finset.sum.{0, 0} (ZMod n) Complex
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                    (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField)))))))
        T fun b =>
        @DFunLike.coe.{1, 1, 1}
          (@AddChar.{0, 0} (ZMod n)
            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          (ZMod n) (fun x => Complex)
          (@AddChar.instFunLike.{0, 0} (ZMod n) Complex
            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
            (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          (@ZMod.stdAddChar n inst)
          (@Neg.neg.{0} (ZMod n)
            (@NegZeroClass.toNeg.{0} (ZMod n)
              (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod n)
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod n)
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod n)
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod n)
                      (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))
            (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
              (@instHMul.{0} (ZMod n)
                (@Distrib.toMul.{0} (ZMod n)
                  (@instDistribOfSemiring.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
              (op a b) k))) := @_root_.Couret.InterIA.SumAutocorr.p2m_local_dft_pairCount

