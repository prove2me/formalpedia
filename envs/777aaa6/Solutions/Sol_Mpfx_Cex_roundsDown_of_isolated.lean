-- Prove2me | solution 1 for Mpfx.Cex.roundsDown_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:58.950338+00:00
-- url     : https://prove2.me/submissions/c0668605-81fa-43bb-971e-1435e5d47b25

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : (h : ℝ) ≤ x) (hx' : x < h + (2 : ℝ) ^ K) :
    RoundsFinite F.unbounded .toNegative x h :=
  ⟨hh, hx, fun v hv hvx => not_lt.mp fun hlt => by
    have := hK v hv (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt⟩
end Mpfx.Cex
