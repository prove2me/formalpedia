-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group349
-- name    : dusart_theta_mesh_generic_group349
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:52:59.45706+00:00
-- url     : https://prove2.me/theorems/7c9f6f94-5678-4a58-8c46-8294ef11d33c
-- title:
--   Verified numerical interval from 4243972352 to 4260749568
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4243972352, 4260749568; 4243898703380725, 4260670833332660).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group349 : DusartNumeric.GenericSpec 4243972352 4260749568 4243898703380725 4260670833332660 := by sorry
