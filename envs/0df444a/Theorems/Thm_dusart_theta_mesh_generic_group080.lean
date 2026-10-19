-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group080
-- name    : dusart_theta_mesh_generic_group080
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:24:50.00598+00:00
-- url     : https://prove2.me/theorems/74b05c9b-2b5d-4651-ac7d-b5e3a74c4741
-- title:
--   Verified numerical interval from 334881024 to 339075328
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(334881024, 339075328; 334862277062422, 339055155623858).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group080 : DusartNumeric.GenericSpec 334881024 339075328 334862277062422 339055155623858 := by sorry
