-- Prove2me | solution 1 for Mpfx.FiniteFormat.isOdd_iff_mem_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:20:20.344182+00:00
-- url     : https://prove2.me/submissions/856d6f8b-13b5-45a9-99c2-a69bbe2425cd

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_not_isEven_and_isOdd
import Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_odd
import Theorems.Thm_Mpfx_FiniteFormat_isEven_iff_even
import Theorems.Thm_Mpfx_FiniteFormat_isEven_iff_mem_shrink
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_mem_unbounded_of_mul_zpow_canonicalExp


set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (hp : F.p ≠ ((1 : ℕ) : Prec))
    (y : Dyadic) :
    F.IsOdd y ↔ y ∈ F.unbounded ∧ y ∉ (F.shrink hp).unbounded := by
  constructor
  · intro h
    obtain ⟨c, hy, -⟩ := (isOdd_iff_odd F hp y).mp h
    exact ⟨F.mem_unbounded_of_mul_zpow_canonicalExp hy,
      fun hC => not_isEven_and_isOdd ((isEven_iff_mem_shrink F hp y).mpr hC) h⟩
  · rintro ⟨hmem, hC⟩
    obtain ⟨c, hc⟩ := F.exists_mul_zpow_canonicalExp hmem
    exact (isOdd_iff_odd F hp y).mpr ⟨c, hc, Int.not_even_iff_odd.mp fun he =>
      hC ((isEven_iff_mem_shrink F hp y).mp ((isEven_iff_even F hp y).mpr ⟨c, hc, he⟩))⟩
end Mpfx.FiniteFormat
