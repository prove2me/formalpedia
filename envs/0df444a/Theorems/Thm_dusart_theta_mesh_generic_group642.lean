-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group642
-- name    : dusart_theta_mesh_generic_group642
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:27:10.547118+00:00
-- url     : https://prove2.me/theorems/0e1ef349-c598-4a3e-a0af-9a40673b8375
-- title:
--   Verified numerical interval from 9159696640 to 9176473856
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9159696640, 9176473856; 9159595659876311, 9176361435348381).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group642 : DusartNumeric.GenericSpec 9159696640 9176473856 9159595659876311 9176361435348381 := by sorry
