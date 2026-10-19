-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group665
-- name    : dusart_theta_mesh_generic_group665
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:30:45.579262+00:00
-- url     : https://prove2.me/theorems/92158ea1-39a4-4701-a8ad-d96a0a5e5a93
-- title:
--   Verified numerical interval from 9545572608 to 9562349824
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9545572608, 9562349824; 9545474271302836, 9562248899246487).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group665 : DusartNumeric.GenericSpec 9545572608 9562349824 9545474271302836 9562248899246487 := by sorry
