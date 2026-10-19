-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group124
-- name    : dusart_theta_mesh_generic_group124
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:28:04.475462+00:00
-- url     : https://prove2.me/theorems/c46c5062-30ce-4279-856a-96afebbee9ef
-- title:
--   Verified numerical interval from 636870912 to 645259520
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(636870912, 645259520; 636850387806200, 645232674583430).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group124 : DusartNumeric.GenericSpec 636870912 645259520 636850387806200 645232674583430 := by sorry
