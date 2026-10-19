-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group236
-- name    : dusart_theta_mesh_generic_group236
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:39:55.52458+00:00
-- url     : https://prove2.me/theorems/a12f9495-68b1-4716-ad5d-6332a5049b6b
-- title:
--   Verified numerical interval from 2348146944 to 2364924160
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2348146944, 2364924160; 2348105604347319, 2364875383755546).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group236 : DusartNumeric.GenericSpec 2348146944 2364924160 2348105604347319 2364875383755546 := by sorry
