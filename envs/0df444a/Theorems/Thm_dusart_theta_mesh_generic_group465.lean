-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group465
-- name    : dusart_theta_mesh_generic_group465
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:05:50.062317+00:00
-- url     : https://prove2.me/theorems/64aa94eb-0e81-4e51-8e91-2a23bf8b99f5
-- title:
--   Verified numerical interval from 6190129408 to 6206906624
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6190129408, 6206906624; 6190077577637012, 6206865834885360).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group465 : DusartNumeric.GenericSpec 6190129408 6206906624 6190077577637012 6206865834885360 := by sorry
