-- Prove2me | solution 1 for Mpfx.IsOdd.transfer_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:24:19.488964+00:00
-- url     : https://prove2.me/submissions/b6e213ab-b41a-4084-815e-5b38d898bd73

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_not_isEven_and_isOdd
import Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_canonical
import Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_mem_shrink
import Theorems.Thm_Mpfx_FiniteFormat_isEven_of_subset
import Theorems.Thm_Mpfx_FiniteFormat_exp_eq_canonicalExp_of_p_one
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_mem_unbounded_of_mem


set_option autoImplicit true
open Mpfx
open FiniteFormat
namespace Mpfx
namespace IsOdd
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁) (hodd : F₂.IsOdd y) :
    F₁.IsOdd y := by
  by_cases hp₁ : F₁.p = ((1 : ℕ) : Prec)
  · have he := exp_eq_canonicalExp_of_p_one hsub hp_F₂ hp₁ hyF₁ hodd
    obtain ⟨c, hc⟩ := F₁.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hyF₁)
    refine (isOdd_iff_canonical F₁ y).mpr
      ⟨fun h => hodd.ne_zero (eq_zero_of_coe_real_zero h), c, hc, ?_⟩
    rw [if_pos hp₁, he, WithBot.unbotD_coe, sub_self, zero_add]
    exact odd_one
  · rw [isOdd_iff_mem_shrink F₁ hp₁]
    exact ⟨mem_unbounded_of_mem hyF₁,
      fun hC => not_isEven_and_isOdd (isEven_of_subset hsub hp_F₂ hyF₁ hC) hodd⟩
end IsOdd
end Mpfx
