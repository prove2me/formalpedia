-- Prove2me | solution 1 for Mpfx.Cex.roundsUp_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:53:06.247722+00:00
-- url     : https://prove2.me/submissions/3e7b7907-1f08-42bb-a4a5-6193df526267

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : (h : ℝ) - (2 : ℝ) ^ K < x) (hx' : x ≤ h) :
    RoundsFinite F.unbounded .toPositive x h :=
  ⟨hh, hx', fun v hv hxv => not_lt.mp fun hlt => by
    have := hK v hv (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt⟩
end Mpfx.Cex
