-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group552
-- name    : dusart_theta_mesh_generic_group552
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:16:00.508006+00:00
-- url     : https://prove2.me/theorems/1460e144-2cc0-4aa7-b472-781ed5e5a6c8
-- title:
--   Verified numerical interval from 7649747200 to 7666524416
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7649747200, 7666524416; 7649627870196018, 7666406384595407).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group552 : DusartNumeric.GenericSpec 7649747200 7666524416 7649627870196018 7666406384595407 := by sorry
