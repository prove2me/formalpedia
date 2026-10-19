-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group177
-- name    : dusart_theta_mesh_generic_group177
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:34:09.009591+00:00
-- url     : https://prove2.me/theorems/97fb3734-f2ca-4e3a-b918-d57017155433
-- title:
--   Verified numerical interval from 1358291200 to 1375068416
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1358291200, 1375068416; 1358264169415383, 1375037742016640).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group177 : DusartNumeric.GenericSpec 1358291200 1375068416 1358264169415383 1375037742016640 := by sorry
