-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group322
-- name    : dusart_theta_mesh_generic_group322
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:49:47.02851+00:00
-- url     : https://prove2.me/theorems/bf0e2e78-0c87-4b4d-9a62-5b26b2042180
-- title:
--   Verified numerical interval from 3790987520 to 3807764736
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3790987520, 3807764736; 3790956007525928, 3807738705948875).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group322 : DusartNumeric.GenericSpec 3790987520 3807764736 3790956007525928 3807738705948875 := by sorry
