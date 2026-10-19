-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group431
-- name    : dusart_theta_mesh_generic_group431
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:02:00.625468+00:00
-- url     : https://prove2.me/theorems/5f92be7b-63f1-46ce-8124-1f54121cf77e
-- title:
--   Verified numerical interval from 5619704064 to 5636481280
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5619704064, 5636481280; 5619638343461148, 5636414126703903).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group431 : DusartNumeric.GenericSpec 5619704064 5636481280 5619638343461148 5636414126703903 := by sorry
