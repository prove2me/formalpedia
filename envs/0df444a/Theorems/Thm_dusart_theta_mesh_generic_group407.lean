-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group407
-- name    : dusart_theta_mesh_generic_group407
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:00:59.284986+00:00
-- url     : https://prove2.me/theorems/f6f2dcfd-8b46-4b66-886a-f95e464b27b3
-- title:
--   Verified numerical interval from 5217050880 to 5233828096
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5217050880, 5233828096; 5216978009563332, 5233757602414955).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group407 : DusartNumeric.GenericSpec 5217050880 5233828096 5216978009563332 5233757602414955 := by sorry
