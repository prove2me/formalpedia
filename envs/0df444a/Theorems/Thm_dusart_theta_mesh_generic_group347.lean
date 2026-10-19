-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group347
-- name    : dusart_theta_mesh_generic_group347
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:59.565579+00:00
-- url     : https://prove2.me/theorems/3bab5d5a-2ea1-4ae4-8415-2d5830d1e38a
-- title:
--   Verified numerical interval from 4210417920 to 4227195136
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4210417920, 4227195136; 4210349551583667, 4227121894215434).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group347 : DusartNumeric.GenericSpec 4210417920 4227195136 4210349551583667 4227121894215434 := by sorry
