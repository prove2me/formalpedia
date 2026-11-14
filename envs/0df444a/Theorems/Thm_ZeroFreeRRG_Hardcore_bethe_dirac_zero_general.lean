-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bethe_dirac_zero_general
-- name    : ZeroFreeRRG.Hardcore.bethe_dirac_zero_general
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:46:42.470237+00:00
-- url     : https://prove2.me/theorems/a68cd3e9-1da3-44a1-bd89-a57c59d64eb1
-- title:
--   Bethe functional vanishes at the replica-symmetric Dirac law
-- statement:
--   For either model, if all spin marginal coordinates are nonzero and their sum is one, then the Bethe functional at the Dirac law concentrated on that marginal equals zero. This verifies the base-point identity used in the compactness argument for the planted-overlap bound.
-- source:
--   Auxiliary model identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.bethe_dirac_zero_general (m : Model) (t : ℝ) (d : ℕ)
    (hπ : ∀ a, m.pi t a ≠ 0) (hsum : (∑ a, m.pi t a) = 1) :
    betheK m t d (diracPi m t) = 0 := by sorry
