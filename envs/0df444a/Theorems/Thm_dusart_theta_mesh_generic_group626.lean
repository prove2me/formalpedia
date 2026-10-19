-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group626
-- name    : dusart_theta_mesh_generic_group626
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:25:21.382868+00:00
-- url     : https://prove2.me/theorems/535f4a87-5b1d-4202-8cbb-5a5ee7af1f1d
-- title:
--   Verified numerical interval from 8891261184 to 8908038400
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8891261184, 8908038400; 8891174447209440, 8907943290773587).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group626 : DusartNumeric.GenericSpec 8891261184 8908038400 8891174447209440 8907943290773587 := by sorry
