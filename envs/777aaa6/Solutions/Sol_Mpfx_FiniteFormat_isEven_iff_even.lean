-- Prove2me | solution 1 for Mpfx.FiniteFormat.isEven_iff_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:13:56.36962+00:00
-- url     : https://prove2.me/submissions/b1302807-d9c7-48fe-a133-8fe2a5b38d82

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_odd
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_mem_unbounded_of_mul_zpow_canonicalExp


set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (hp : F.p ≠ ((1 : ℕ) : Prec)) (y : Dyadic) :
    F.IsEven y ↔ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧ Even c := by
  constructor
  · rintro ⟨hmem, hodd⟩
    obtain ⟨c, hc⟩ := F.exists_mul_zpow_canonicalExp hmem
    exact ⟨c, hc, Int.not_odd_iff_even.mp fun ho => hodd ((isOdd_iff_odd F hp y).mpr ⟨c, hc, ho⟩)⟩
  · rintro ⟨c, hc, he⟩
    refine ⟨F.mem_unbounded_of_mul_zpow_canonicalExp hc, fun ho => ?_⟩
    obtain ⟨c', hc', ho'⟩ := (isOdd_iff_odd F hp y).mp ho
    have hcc : c = c' := by
      exact_mod_cast mul_right_cancel₀ (zpow_ne_zero _ two_ne_zero) (hc.symm.trans hc')
    exact Int.not_even_iff_odd.mpr ho' (hcc ▸ he)
end Mpfx.FiniteFormat
