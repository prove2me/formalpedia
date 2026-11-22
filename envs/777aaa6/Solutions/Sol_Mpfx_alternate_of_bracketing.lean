-- Prove2me | solution 1 for Mpfx.alternate_of_bracketing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:25:17.883198+00:00
-- url     : https://prove2.me/submissions/4032b373-2cb3-47b7-938c-7a5bfb9c153a

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_floor_add_one
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_eq_floor
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_neighbors_alternate
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    (F.IsOdd y' ↔ ¬ F.IsOdd y) ∧ (¬ F.IsEven y → F.IsEven y') := by
  set e := F.canonicalExp x with he
  set s := x * (2 : ℝ) ^ (-e) with hs
  have hy_eq : y = Dyadic.ofIntZpow ⌊s⌋ e := RoundsFinite.toNegative_eq_floor F x hy
  -- `x ≠ y` says exactly that `⌊s⌋ ≠ s`.
  have h_lo_ne_s : (⌊s⌋ : ℝ) ≠ s := by
    intro hcon
    exact hne (by rw [hy_eq, Dyadic.coe_ofIntZpow, hcon, hs, mul_zpow_neg_self])
  have hy'_eq : y' = Dyadic.ofIntZpow (⌊s⌋ + 1) e :=
    RoundsFinite.unique_toPositive hy' (RoundsFinite.toPositive_floor_add_one F h_lo_ne_s)
  have h1 : F.IsOdd y' ↔ ¬ F.IsOdd y := by
    rw [hy_eq, hy'_eq]; exact neighbors_alternate x h h_lo_ne_s
  exact ⟨h1, fun hev => ⟨hy'.1, fun ho => hev ⟨hy.1, h1.mp ho⟩⟩⟩
end Mpfx
