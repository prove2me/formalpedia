-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_scaled_phase_perturbation
-- name    : ZeroFreeRRG.Hardcore.scaled_phase_perturbation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:09:48.286205+00:00
-- url     : https://prove2.me/theorems/f98693d7-0183-41eb-9db1-8ce5a57e3b79
-- title:
--   Relative complex perturbation controls phase change
-- statement:
--   If $z\ne0$, $0\le r\le96/625$, and $|z-w|\le r|z|$, then $w\ne0$ and the normalized phases differ by at most $(25/23)r$.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.scaled_phase_perturbation (z w : ℂ) (r : ℝ) (hz : z ≠ 0)
    (hr0 : 0 ≤ r) (hr : r ≤ 96/625) (hclose : ‖z-w‖ ≤ r*‖z‖) :
    w ≠ 0 ∧ ‖z/(‖z‖:ℂ)-w/(‖w‖:ℂ)‖ ≤ (25/23)*r := by sorry
