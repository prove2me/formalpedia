-- Prove2me | solution 1 for Mpfx.round_round_mid_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:48:43.18649+00:00
-- url     : https://prove2.me/submissions/be9a36f5-9585-4cfd-9c25-bab9c9d2f037

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Theorems.Thm_P2M_Mpfx_rnd_lt_mid__f8e65c434f46
import Theorems.Thm_Mpfx_rnd_gt_mid_robust
import Theorems.Thm_Mpfx_rndUp_le_rndDown_add_ulp


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w)
    (hcmid : |x - midp F₁ x| ≤ ulp F₂ x / 2 →
      RoundsFinite F₁.unbounded (.nearest tb₁) x w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  have hmidp : midp F₁ x = (rndDown F₁ x : ℝ) + ulp F₁ x / 2 := rfl
  rcases lt_or_ge (x - (rndDown F₁ x : ℝ)) ((ulp F₁ x - ulp F₂ x) / 2) with hlt | hge
  · -- more than `½·ulp₂` below the midpoint
    refine rnd_lt_mid' hundef₁ hx h21 hle ?_ hz hw
    rw [hmidp]; linarith
  · rcases lt_or_ge ((ulp F₁ x + ulp F₂ x) / 2) (x - (rndDown F₁ x : ℝ)) with hgt | hmid
    · -- more than `½·ulp₂` above the midpoint
      refine rnd_gt_mid_robust hundef₁ hx h21 hle ?_ hz hw
      have hup := rndUp_le_rndDown_add_ulp F₁ x
      linarith
    · -- within `½·ulp₂` of the midpoint
      refine hcmid ?_
      rw [abs_le, hmidp]; exact ⟨by linarith, by linarith⟩
end Mpfx
