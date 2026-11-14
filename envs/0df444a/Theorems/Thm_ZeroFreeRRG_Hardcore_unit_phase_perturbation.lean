-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_unit_phase_perturbation
-- name    : ZeroFreeRRG.Hardcore.unit_phase_perturbation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:09:45.775616+00:00
-- url     : https://prove2.me/theorems/fe43e612-e2ef-4a6e-87f8-443ff1837d5f
-- title:
--   Phase change under a small perturbation of a unit complex number
-- statement:
--   A perturbation of a unit complex number by at most $r\le96/625$ remains nonzero and changes its normalized phase by at most $(25/23)r$.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.unit_phase_perturbation (u v : ℂ) (r : ℝ) (hu : ‖u‖ = 1)
    (hr0 : 0 ≤ r) (hr : r ≤ 96/625) (hclose : ‖u-v‖ ≤ r) :
    v ≠ 0 ∧ ‖u-v/(‖v‖:ℂ)‖ ≤ (25/23)*r := by sorry
