-- Prove2me | solution 1 for Couret.InterIA.Cubic.square_cube_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:58:32.934557+00:00
-- url     : https://prove2.me/submissions/d4da93cf-3e8b-415c-ac7b-7e5f960a9057

import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Cubic_dft_cconv
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset





theorem square_cube_scalar_injective {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b : R) (hs : a^2=b^2) (hc : a^3=b^3) : a=b := by
  by_cases hb : b^2=0
  · have ha0 : a=0 := eq_zero_of_pow_eq_zero (hs.trans hb)
    have hb0 : b=0 := eq_zero_of_pow_eq_zero hb
    simp [ha0,hb0]
  · apply mul_right_cancel₀ hb
    calc a*b^2 = a*a^2 := by rw [hs]
         _ = a^3 := by ring
         _ = b^3 := hc
         _ = b*b^2 := by ring

theorem p2m_local_square_cube_injective {n : ℕ} [NeZero n] (f g : ZMod n → ℂ)
    (hs : cconv f f = cconv g g)
    (hc : cconv (cconv f f) f = cconv (cconv g g) g) : f=g := by
  apply ZMod.dft.injective
  funext k
  apply square_cube_scalar_injective
  · have h := congrFun (congrArg ZMod.dft hs) k
    simpa only [dft_cconv,pow_two] using h
  · have h := congrFun (congrArg ZMod.dft hc) k
    simp only [dft_cconv] at h
    simpa only [pow_succ,pow_two,pow_zero,one_mul] using h

end Couret.InterIA.Cubic

theorem solution : ∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] (f g : ZMod n → Complex),
  @Eq.{1} (ZMod n → Complex)
      (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
        (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
        (ZMod.decidableEq n) f f)
      (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
        (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
        (ZMod.decidableEq n) g g) →
    @Eq.{1} (ZMod n → Complex)
        (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
          (ZMod.decidableEq n)
          (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
            (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
            (ZMod.decidableEq n) f f)
          f)
        (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
          (ZMod.decidableEq n)
          (@Couret.InterIA.Cubic.cconv.{0} (ZMod n)
            (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (@ZMod.fintype n inst)
            (ZMod.decidableEq n) g g)
          g) →
      @Eq.{1} (ZMod n → Complex) f g := @_root_.Couret.InterIA.Cubic.p2m_local_square_cube_injective

