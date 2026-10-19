-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group320
-- name    : dusart_theta_mesh_generic_group320
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:49:45.619977+00:00
-- url     : https://prove2.me/theorems/717ffccf-ba1b-4780-9105-b044f702405f
-- title:
--   Verified numerical interval from 3757433088 to 3774210304
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3757433088, 3774210304; 3757402846715530, 3774185101143134).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group320 : DusartNumeric.GenericSpec 3757433088 3774210304 3757402846715530 3774185101143134 := by sorry
