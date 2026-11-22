-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies_toOdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:25:30.378194+00:00
-- url     : https://prove2.me/submissions/5b8e28c8-4ad8-4bc8-8a7b-57f721546c24

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_RoundsFinite_self
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_floor_add_one
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_neighbors_alternate
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  have hd := RoundsFinite.toNegative_floor F x
  change RoundsFinite F.unbounded .toOdd x
    (Dyadic.ofIntZpow (if (⌊s⌋ : ℝ) = s then ⌊s⌋
      else if F.IsOdd (Dyadic.ofIntZpow ⌊s⌋ e) then ⌊s⌋ else ⌊s⌋ + 1) e)
  split_ifs with hs hodd
  · -- An integer scaled mantissa: the floor point is `x`.
    have hx : x = (Dyadic.ofIntZpow ⌊s⌋ e : ℝ) := by
      rw [Dyadic.coe_ofIntZpow, hs, mul_zpow_neg_self]
    have := RoundsFinite.self (F := F.unbounded) .toOdd hd.1
    rwa [← hx] at this
  · exact ⟨hd.1, Or.inl hd, fun _ => hodd⟩
  · have hu := RoundsFinite.toPositive_floor_add_one F hs
    exact ⟨hu.1, Or.inr hu, fun _ => (neighbors_alternate x h hs).mpr hodd⟩
end Mpfx
