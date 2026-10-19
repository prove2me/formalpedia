-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group343
-- name    : dusart_theta_mesh_generic_group343
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:52:32.883113+00:00
-- url     : https://prove2.me/theorems/99bf71e5-5f57-4ed8-8794-7276f36b5f2f
-- title:
--   Verified numerical interval from 4143309056 to 4160086272
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4143309056, 4160086272; 4143248562823574, 4160027440691635).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group343 : DusartNumeric.GenericSpec 4143309056 4160086272 4143248562823574 4160027440691635 := by sorry
