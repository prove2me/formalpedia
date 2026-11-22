-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.vector_radius_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:19.625379+00:00
-- url     : https://prove2.me/submissions/4977194f-d159-40b3-bb9a-5e3c5d3ca897

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_Kourovka_Polyhedral_Radius
import Theorems.Thm_Kourovka_MetabelianEnumeration_radius_shrink

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v u : E) (C D ρ δ : ℝ)
    (hC : 0 < C) (hρC : C < ρ) (hρD : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4)
    (hr : ρ ≤ ‖v‖) (hr' : ‖v‖ < ρ + δ)
    (hu : ‖u‖ ^ 2 ≤ D ^ 2) (hdot : inner ℝ v u ≤ -C * ‖v‖) :
    ‖v + u‖ < ρ := by
  have hs : ‖v + u‖ ^ 2 ≤ ‖v‖ ^ 2 - 2 * C * ‖v‖ + D ^ 2 := by
    rw [norm_add_sq_real]
    nlinarith
  have h := radius_shrink C D ρ δ ‖v‖ (‖v + u‖ ^ 2)
    hC hρC hρD hδ hδC hr hr' hs
  nlinarith [norm_nonneg (v + u)]
end Kourovka.MetabelianEnumeration
