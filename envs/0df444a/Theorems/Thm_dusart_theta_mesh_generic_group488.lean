-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group488
-- name    : dusart_theta_mesh_generic_group488
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:09:00.322985+00:00
-- url     : https://prove2.me/theorems/c7d722d9-eb4a-4844-9664-90c19a261e04
-- title:
--   Verified numerical interval from 6576005376 to 6592782592
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6576005376, 6592782592; 6575938367990992, 6592716179626600).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group488 : DusartNumeric.GenericSpec 6576005376 6592782592 6575938367990992 6592716179626600 := by sorry
