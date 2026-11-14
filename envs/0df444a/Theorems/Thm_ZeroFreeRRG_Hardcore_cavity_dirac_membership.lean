-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_dirac_membership
-- name    : ZeroFreeRRG.Hardcore.cavity_dirac_membership
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:45:50.037029+00:00
-- url     : https://prove2.me/theorems/d0c6593a-ecd4-47e4-81ba-1ea5c856c820
-- title:
--   The replica-symmetric point lies in the cavity-law domain
-- statement:
--   If the model marginal belongs to the simplex, its Dirac law belongs to the cavity-law domain: it is supported on the simplex and has the prescribed mean.
-- source:
--   Auxiliary model identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.cavity_dirac_membership (m : Model) (t : ℝ) (hπ : m.pi t ∈ stdSimplex ℝ m.Spin) :
    diracPi m t ∈ cavityLaws m t := by sorry
