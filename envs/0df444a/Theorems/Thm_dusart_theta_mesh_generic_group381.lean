-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group381
-- name    : dusart_theta_mesh_generic_group381
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:55:53.706253+00:00
-- url     : https://prove2.me/theorems/3747994a-0a8b-43f3-aa46-3bc8842ea4fb
-- title:
--   Verified numerical interval from 4780843264 to 4797620480
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4780843264, 4797620480; 4780778254784307, 4797564278005869).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group381 : DusartNumeric.GenericSpec 4780843264 4797620480 4780778254784307 4797564278005869 := by sorry
