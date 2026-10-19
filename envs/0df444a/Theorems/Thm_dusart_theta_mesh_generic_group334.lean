-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group334
-- name    : dusart_theta_mesh_generic_group334
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:59.984526+00:00
-- url     : https://prove2.me/theorems/aa43c8a7-803a-495b-a320-a6ce042eb1a1
-- title:
--   Verified numerical interval from 3992314112 to 4009091328
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3992314112, 4009091328; 3992262620822063, 4009045358044043).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group334 : DusartNumeric.GenericSpec 3992314112 4009091328 3992262620822063 4009045358044043 := by sorry
