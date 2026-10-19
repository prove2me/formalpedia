-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group654
-- name    : dusart_theta_mesh_generic_group654
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:29:45.76329+00:00
-- url     : https://prove2.me/theorems/7fd52ca1-d3cb-4479-a9dd-92a08febf656
-- title:
--   Verified numerical interval from 9361023232 to 9377800448
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9361023232, 9377800448; 9360932758300406, 9377698979977643).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group654 : DusartNumeric.GenericSpec 9361023232 9377800448 9360932758300406 9377698979977643 := by sorry
