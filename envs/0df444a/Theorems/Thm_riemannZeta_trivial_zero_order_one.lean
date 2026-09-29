-- Prove2me | Theorems.Thm_riemannZeta_trivial_zero_order_one
-- name    : riemannZeta_trivial_zero_order_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:35:55.531263+00:00
-- url     : https://prove2.me/theorems/68c51725-93cf-497b-adfc-463110b2976d
-- title:
--   The trivial zeros of the Riemann zeta function are simple
-- statement:
--   Every negative even zero of the Riemann zeta function has analytic order exactly one. Equivalently, all trivial zeros of the zeta function are simple.
-- source:
--   Classical consequence of the completed-zeta factorization and the simple poles of the Gamma factor at negative even integers.

import Mathlib
import Theorems.Thm_invGammaR_neg_even_deriv_ne_zero

open Complex Topology

theorem riemannZeta_trivial_zero_order_one (n : ℕ) :
    analyticOrderAt riemannZeta (-2 * ((n + 1 : ℕ) : ℂ)) = (1 : ℕ∞) := by sorry
