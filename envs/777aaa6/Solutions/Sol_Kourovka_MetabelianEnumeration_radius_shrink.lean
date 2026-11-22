-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.radius_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:21.989709+00:00
-- url     : https://prove2.me/submissions/b2f17d79-add2-4ea2-a961-22248b5e40bd

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_Kourovka_Polyhedral_Radius

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution (C D ρ δ r s : ℝ)
    (_hC : 0 < C) (hρC : C < ρ) (hρD : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4)
    (hr : ρ ≤ r) (hr' : r < ρ + δ)
    (hs : s ≤ r ^ 2 - 2 * C * r + D ^ 2) : s < ρ ^ 2 := by
  have hsum : 0 < ρ + δ + r - 2 * C := by linarith
  have hstep := mul_pos (sub_pos.mpr hr') hsum
  have hδquad : δ ^ 2 - 2 * C * δ ≤ 0 := by
    nlinarith [mul_nonneg (le_of_lt hδ) (show 0 ≤ 2 * C - δ by linarith)]
  have hmargin := mul_nonneg (show 0 ≤ C / 4 - δ by linarith)
    (show 0 ≤ ρ by linarith)
  nlinarith
end Kourovka.MetabelianEnumeration
