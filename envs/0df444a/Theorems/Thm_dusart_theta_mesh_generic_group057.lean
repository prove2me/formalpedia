-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group057
-- name    : dusart_theta_mesh_generic_group057
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:14:30.950992+00:00
-- url     : https://prove2.me/theorems/c07ce2d2-3cd0-4225-a418-9ff5585e2171
-- title:
--   Verified numerical interval from 238412032 to 242606336
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(238412032, 242606336; 238400570893257, 242592680640313).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group057 : DusartNumeric.GenericSpec 238412032 242606336 238400570893257 242592680640313 := by sorry
