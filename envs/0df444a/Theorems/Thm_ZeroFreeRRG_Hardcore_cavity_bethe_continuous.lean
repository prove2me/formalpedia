-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_bethe_continuous
-- name    : ZeroFreeRRG.Hardcore.cavity_bethe_continuous
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:54:18.481675+00:00
-- url     : https://prove2.me/theorems/6a841adb-52fe-4ad4-907c-83846092bf02
-- title:
--   Continuity of the Bethe functional on cavity laws
-- statement:
--   For either spin model, every real parameter and every integer degree, the Bethe functional is continuous on the cavity-law domain in the weak topology. This is the continuity input used with compactness and Condition 1 in the proof of the exponential planted-overlap bound.
-- source:
--   Auxiliary analytic property for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set Filter ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.cavity_bethe_continuous (m : Model) (t : ℝ) (d : ℕ) :
    ContinuousOn (betheK m t d) (cavityLaws m t) := by sorry
