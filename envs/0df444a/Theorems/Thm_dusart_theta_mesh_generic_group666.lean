-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group666
-- name    : dusart_theta_mesh_generic_group666
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:30:47.19636+00:00
-- url     : https://prove2.me/theorems/5d86571d-867f-464f-8285-aa095b1862f8
-- title:
--   Verified numerical interval from 9562349824 to 9579127040
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9562349824, 9579127040; 9562248899246487, 9579029449772796).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group666 : DusartNumeric.GenericSpec 9562349824 9579127040 9562248899246487 9579029449772796 := by sorry
