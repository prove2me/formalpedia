-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group429
-- name    : dusart_theta_mesh_generic_group429
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:01:51.324415+00:00
-- url     : https://prove2.me/theorems/a916da62-0057-42a5-8ceb-b08906e8d6b5
-- title:
--   Verified numerical interval from 5586149632 to 5602926848
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5586149632, 5602926848; 5586073789076650, 5602846383540528).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group429 : DusartNumeric.GenericSpec 5586149632 5602926848 5586073789076650 5602846383540528 := by sorry
