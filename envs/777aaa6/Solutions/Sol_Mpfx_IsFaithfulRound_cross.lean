-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:02:09.386665+00:00
-- url     : https://prove2.me/submissions/3b90dacc-b180-4a39-afd1-b996378666bd

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic} (hx : x ≤ x')
    (hy : IsFaithfulRound F x y) (hy' : IsFaithfulRound F x' y') (hlt : (y' : ℝ) < y) :
    RoundsFinite F .toPositive x y ∧ RoundsFinite F .toPositive x' y ∧
      RoundsFinite F .toNegative x y' ∧ RoundsFinite F .toNegative x' y' ∧
        x' < y ∧ (y' : ℝ) ≤ x := by
  rcases hy with ⟨hym, hyx, -⟩ | ⟨hym, hxy, hymin⟩ <;>
    rcases hy' with ⟨hym', hyx', hymax'⟩ | ⟨hym', hxy', hymin'⟩
  · exact absurd (hymax' y hym (hyx.trans hx)) (not_le.mpr hlt)
  · exact absurd (hyx.trans (hx.trans hxy')) (not_le.mpr hlt)
  · have hx'y : x' < y := lt_of_not_ge fun h => absurd (hymax' y hym h) (not_le.mpr hlt)
    have hy'x : (y' : ℝ) ≤ x :=
      le_of_not_gt fun h => absurd (hymin y' hym' h.le) (not_le.mpr hlt)
    exact ⟨⟨hym, hxy, hymin⟩, ⟨hym, hx'y.le, fun z hz hz' => hymin z hz (hx.trans hz')⟩,
      ⟨hym', hy'x, fun z hz hz' => hymax' z hz (hz'.trans hx)⟩, ⟨hym', hyx', hymax'⟩,
      hx'y, hy'x⟩
  · exact absurd (hymin y' hym' (hx.trans hxy')) (not_le.mpr hlt)
end IsFaithfulRound
end Mpfx
