-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_unit_chord_projection
-- name    : ZeroFreeRRG.Hardcore.unit_chord_projection
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:52:25.185201+00:00
-- url     : https://prove2.me/theorems/58da7194-9a53-43df-a000-e339706fbbef
-- title:
--   Unit complex vectors close in chord have large projection
-- statement:
--   If unit complex numbers $u,v$ have $|u-v|\le1/2$, then $\operatorname{Re}(\overline u v)\ge7/8$. This supplies a quantitative sector bound.
-- source:
--   Auxiliary complex geometry for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem ZeroFreeRRG.Hardcore.unit_chord_projection (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hclose : ‖u-v‖ ≤ 1/2) : (7:ℝ)/8 ≤ (star u*v).re := by sorry
