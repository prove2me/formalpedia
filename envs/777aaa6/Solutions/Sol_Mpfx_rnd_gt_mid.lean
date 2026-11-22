-- Prove2me | solution 1 for Mpfx.rnd_gt_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:46:02.328929+00:00
-- url     : https://prove2.me/submissions/4a720553-f961-4617-83c6-bc1f022dfbc4

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Theorems.Thm_Mpfx_rnd_lt_mid
import Theorems.Thm_Mpfx_rndNeg
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_canonicalExp_neg
import Theorems.Thm_Mpfx_rndDown_neg_real
import Theorems.Thm_Mpfx_ulp_neg
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.ulp_neg



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : x ≠ 0)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hmid : (rndUp F₁ x : ℝ) - ulp F₁ x / 2 + ulp F₂ x / 2 < x)
    (hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  have h21' : F₂.canonicalExp (-x) < F₁.canonicalExp (-x) := by
    rw [canonicalExp_neg, canonicalExp_neg]; exact h21
  have hmid' : -x < midp F₁ (-x) - ulp F₂ (-x) / 2 := by
    unfold midp; rw [rndDown_neg_real, ulp_neg, ulp_neg]; linarith [hmid]
  have hcexp' : F₁.canonicalExp ((-z : Dyadic) : ℝ) = F₁.canonicalExp (-x) := by
    rw [Dyadic.coe_real_neg, canonicalExp_neg, canonicalExp_neg]; exact hcexp
  exact rndNeg hz hw (rnd_lt_mid hundef₁ (neg_ne_zero.mpr hx) h21' hmid' hcexp')
end Mpfx
