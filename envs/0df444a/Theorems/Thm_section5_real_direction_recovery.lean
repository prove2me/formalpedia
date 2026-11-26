-- Prove2me | Theorems.Thm_section5_real_direction_recovery
-- name    : section5_real_direction_recovery
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:41.721087+00:00
-- url     : https://prove2.me/theorems/7450deb2-7e7e-51f9-8c18-110fde7e9171
-- title:
--   Recovery of a real direction from an approximate complex multiple
-- statement:
--   Let $v\in\mathbb C^n$ and $w\in\mathbb R^n$ be unit vectors, let $\zeta\in\mathbb C$, and suppose $0<\varepsilon<1$ and $\|v-\zeta w\|\le\varepsilon/24$, using the coordinatewise complex embedding of $w$. Let $a=\operatorname{Re}v$, $b=\operatorname{Im}v$, and choose $r=a$ if $\|b\|\le\|a\|$, otherwise $r=b$. Then
--
--   $$
--   r\ne0,\qquad \min\left\{\left\|\frac r{\|r\|}-w\right\|,\left\|\frac r{\|r\|}+w\right\|\right\}\le\varepsilon/6.
--   $$
--
--   This converts complex-vector recovery into recovery of a real direction up to sign.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5PhaseRecovery.lean, section5_real_direction_recovery, lines 45–96.

import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_section5_normalize_real_direction
set_option autoImplicit false

theorem section5_real_direction_recovery {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (ζ : ℂ) (ε : ℝ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hε : 0 < ε) (hε' : ε < 1)
    (hclose : ‖v - ζ • section5_complexify w‖ ≤ ε/24) :
    let a := section5_real_part v
    let b := section5_imag_part v
    let r := if ‖b‖ ≤ ‖a‖ then a else b
    r ≠ 0 ∧
      (‖‖r‖⁻¹ • r - w‖ ≤ ε/6 ∨ ‖‖r‖⁻¹ • r + w‖ ≤ ε/6) := by sorry
