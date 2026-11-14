-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_laws_compact
-- name    : ZeroFreeRRG.Hardcore.cavity_laws_compact
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:51:36.218523+00:00
-- url     : https://prove2.me/theorems/a75c514f-19f2-4097-bee6-ec06efe78bfa
-- title:
--   Compactness of the cavity-law domain
-- statement:
--   For either spin model and every real parameter, the set of probability measures supported on the spin simplex with the prescribed coordinate means is compact in the weak topology.
-- source:
--   Auxiliary analytic property for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set Filter ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.cavity_laws_compact (m : Model) (t : ℝ) : IsCompact (cavityLaws m t) := by sorry
