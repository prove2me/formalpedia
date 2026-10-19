-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group596
-- name    : dusart_theta_mesh_generic_group596
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:21:27.622859+00:00
-- url     : https://prove2.me/theorems/abb0ddb1-db59-4518-9c73-a3c7488bb875
-- title:
--   Verified numerical interval from 8387944704 to 8404721920
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8387944704, 8404721920; 8387876049789313, 8404655156748157).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group596 : DusartNumeric.GenericSpec 8387944704 8404721920 8387876049789313 8404655156748157 := by sorry
