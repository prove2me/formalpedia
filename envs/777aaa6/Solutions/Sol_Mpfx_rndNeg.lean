-- Prove2me | solution 1 for Mpfx.rndNeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:09.448257+00:00
-- url     : https://prove2.me/submissions/8b9fb8d9-6ae7-466a-8c71-447c07b32f99

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_RoundsFinite_neg_nearest
attribute [local simp] Mpfx.Dyadic.coe_real_neg



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {v : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) v z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w)
    (hbase : RoundsFinite F₂.unbounded (.nearest tb₂) (-v) (-z) →
      RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) →
      RoundsFinite F₁.unbounded (.nearest tb₁) (-v) (-w)) :
    RoundsFinite F₁.unbounded (.nearest tb₁) v w := by
  have hz' : RoundsFinite F₂.unbounded (.nearest tb₂) (-v) (-z) :=
    (RoundsFinite.neg_nearest F₂.unbounded tb₂ v z).mp hz
  have hw' : RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) := by
    rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ (z : ℝ) w).mp hw
  exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ v w).mpr (hbase hz' hw')
end Mpfx
