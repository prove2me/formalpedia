-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group310
-- name    : dusart_theta_mesh_generic_group310
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:48:54.668922+00:00
-- url     : https://prove2.me/theorems/738b580e-b402-4825-8982-d7df317a8c9f
-- title:
--   Verified numerical interval from 3589660928 to 3606438144
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3589660928, 3606438144; 3589612528997503, 3606385291529080).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group310 : DusartNumeric.GenericSpec 3589660928 3606438144 3589612528997503 3606385291529080 := by sorry
