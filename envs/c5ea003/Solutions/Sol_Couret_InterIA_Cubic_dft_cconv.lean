-- Prove2me | solution 1 for Couret.InterIA.Cubic.dft_cconv
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:54.578496+00:00
-- url     : https://prove2.me/submissions/00603b8d-db9b-4ad3-b313-14d2c21a0c7e

import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset



theorem p2m_local_dft_cconv {n : ℕ} [NeZero n] (f g : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft (cconv f g) k = ZMod.dft f k * ZMod.dft g k := by
  classical
  calc
    _ = ∑ x : ZMod n, ∑ y : ZMod n, ∑ z : ZMod n,
        ZMod.stdAddChar (-(z*k)) * (if x+y=z then f x*g y else 0) := by
      simp only [ZMod.dft_apply,cconv,smul_eq_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x : ZMod n, ∑ y : ZMod n,
        ZMod.stdAddChar (-((x+y)*k)) * (f x*g y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp [mul_ite,eq_comm]
    _ = _ := by
      simp only [ZMod.dft_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [add_mul,neg_add,AddChar.map_add_eq_mul]
      ring





end Couret.InterIA.Cubic

theorem solution : ∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] (f g : ZMod n → Complex)
  (k : ZMod n),
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
      (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
        (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
        (ZMod.decidableEq n) f g)
      k)
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
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
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (ZMod n → Complex) (ZMod n → Complex)
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
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (ZMod n → Complex) (ZMod n → Complex)
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
        (@ZMod.dft.{0} n inst Complex Complex.addCommGroup (@Semiring.toModule.{0} Complex Complex.instSemiring)) f k)
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
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (ZMod n → Complex) (ZMod n → Complex)
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
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring)
            (@RingHomInvPair.ids.{0} Complex Complex.instSemiring) (ZMod n → Complex) (ZMod n → Complex)
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
        (@ZMod.dft.{0} n inst Complex Complex.addCommGroup (@Semiring.toModule.{0} Complex Complex.instSemiring)) g k)) := @_root_.Couret.InterIA.Cubic.p2m_local_dft_cconv

