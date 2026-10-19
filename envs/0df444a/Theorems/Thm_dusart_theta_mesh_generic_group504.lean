-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group504
-- name    : dusart_theta_mesh_generic_group504
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:10:11.998992+00:00
-- url     : https://prove2.me/theorems/cd7ed8ec-eaa3-44b7-ac60-c5a118594d08
-- title:
--   Verified numerical interval from 6844440832 to 6861218048
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6844440832, 6861218048; 6844377176576405, 6861154497758265).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group504 : DusartNumeric.GenericSpec 6844440832 6861218048 6844377176576405 6861154497758265 := by sorry
