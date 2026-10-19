-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group280
-- name    : dusart_theta_mesh_generic_group280
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:45:30.452281+00:00
-- url     : https://prove2.me/theorems/23caa376-806d-4acc-a413-2a4bc9f2b93c
-- title:
--   Verified numerical interval from 3086344448 to 3103121664
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3086344448, 3103121664; 3086296994856454, 3103056878052544).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group280 : DusartNumeric.GenericSpec 3086344448 3103121664 3086296994856454 3103056878052544 := by sorry
