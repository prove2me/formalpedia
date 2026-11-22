-- Prove2me | solution 1 for Mpfx.roundsRTO_RTO_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:25:28.574037+00:00
-- url     : https://prove2.me/submissions/da1d599b-a9db-4a72-92eb-9b596be6b2a4

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_IsFaithfulRound_iff_of_between
import Theorems.Thm_Mpfx_IsFaithfulRound_of_subset
import Theorems.Thm_Mpfx_IsOdd_transfer_of_subset
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
attribute [local simp] Mpfx.Dyadic.coe_real_inj



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toOdd (z : ℝ) w') :
    RoundsFinite F₁ .toOdd x w' := by
  obtain ⟨hzF₂, hz_faithful, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw_faithful, hw_odd_imp⟩ := hw
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · rw [hzx] at hw_faithful hw_odd_imp
    exact ⟨hw'F₁, hw_faithful, hw_odd_imp⟩
  · have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    rcases eq_or_ne z w' with hzw | hzw
    · -- z = w': w' is x's F₁-rounding directly via hz's faithfulness, and
      -- its F₁-oddness comes from F₂-oddness via RTO-padding transfer.
      subst hzw
      refine ⟨hw'F₁, hz_faithful.of_subset hsub hw'F₁, ?_⟩
      · exact fun _ => IsOdd.transfer_of_subset hsub hp_F₂ hw'F₁ (hz_odd_imp hxne)
    · -- z ≠ w': `z ∉ F₁` (else RTO in `F₁` fixes it), so `x` and `z` share their
      -- faithful roundings in `F₁`.
      have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := fun h_eq => hzw (Dyadic.coe_real_inj z w' |>.mp h_eq)
      have hz₁ : z ∉ F₁ := fun h =>
        hzw (RoundsFinite.eq_of_mem (rm := .toOdd) h ⟨hw'F₁, hw_faithful, hw_odd_imp⟩).symm
      refine ⟨hw'F₁, (IsFaithfulRound.iff_of_between hsub hz_faithful hz₁ w').mpr hw_faithful, ?_⟩
      · -- Parity: from `hw`'s own parity clause (z ≠ w').
        intro _
        exact hw_odd_imp hz_ne_w'
end Mpfx
