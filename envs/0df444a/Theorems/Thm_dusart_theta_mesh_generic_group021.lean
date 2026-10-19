-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group021
-- name    : dusart_theta_mesh_generic_group021
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:10:46.499561+00:00
-- url     : https://prove2.me/theorems/8d032ce7-051b-4478-9e90-96aaa6b1ef89
-- title:
--   Verified numerical interval from 144040192 to 146137344
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(144040192, 146137344; 144031811556532, 146128928829240).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group021 : DusartNumeric.GenericSpec 144040192 146137344 144031811556532 146128928829240 := by sorry
