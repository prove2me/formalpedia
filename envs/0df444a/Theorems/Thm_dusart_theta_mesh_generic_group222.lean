-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group222
-- name    : dusart_theta_mesh_generic_group222
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:37:43.21649+00:00
-- url     : https://prove2.me/theorems/d4d60d6f-e24c-4a83-aaf1-dd111f1c0156
-- title:
--   Verified numerical interval from 2113265920 to 2130043136
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2113265920, 2130043136; 2113235110363146, 2129999298941350).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group222 : DusartNumeric.GenericSpec 2113265920 2130043136 2113235110363146 2129999298941350 := by sorry
