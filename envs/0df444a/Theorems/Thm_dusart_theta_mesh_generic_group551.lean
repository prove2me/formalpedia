-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group551
-- name    : dusart_theta_mesh_generic_group551
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:15:47.999994+00:00
-- url     : https://prove2.me/theorems/f2b64c07-7747-4140-b395-d144b3c373ed
-- title:
--   Verified numerical interval from 7632969984 to 7649747200
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7632969984, 7649747200; 7632859028840772, 7649627870196018).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group551 : DusartNumeric.GenericSpec 7632969984 7649747200 7632859028840772 7649627870196018 := by sorry
