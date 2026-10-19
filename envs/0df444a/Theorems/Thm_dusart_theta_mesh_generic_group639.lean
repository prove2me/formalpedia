-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group639
-- name    : dusart_theta_mesh_generic_group639
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:27:53.248596+00:00
-- url     : https://prove2.me/theorems/3d5e17f1-820f-4f36-8752-b7a0551ffacb
-- title:
--   Verified numerical interval from 9109364992 to 9126142208
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9109364992, 9126142208; 9109271493254758, 9126052554537223).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group639 : DusartNumeric.GenericSpec 9109364992 9126142208 9109271493254758 9126052554537223 := by sorry
