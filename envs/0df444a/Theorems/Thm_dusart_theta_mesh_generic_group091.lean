-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group091
-- name    : dusart_theta_mesh_generic_group091
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:26:07.471985+00:00
-- url     : https://prove2.me/theorems/e5b84e7a-8dc0-4be2-baf4-ab29e97e76dc
-- title:
--   Verified numerical interval from 381018368 to 385212672
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(381018368, 385212672; 381007879765648, 385199025489431).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group091 : DusartNumeric.GenericSpec 381018368 385212672 381007879765648 385199025489431 := by sorry
