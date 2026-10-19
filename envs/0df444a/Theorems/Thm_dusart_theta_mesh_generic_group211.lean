-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group211
-- name    : dusart_theta_mesh_generic_group211
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:36:15.790986+00:00
-- url     : https://prove2.me/theorems/e596536d-0f96-45d2-99e1-1f92856f62b3
-- title:
--   Verified numerical interval from 1928716544 to 1945493760
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1928716544, 1945493760; 1928660084942988, 1945437962943639).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group211 : DusartNumeric.GenericSpec 1928716544 1945493760 1928660084942988 1945437962943639 := by sorry
