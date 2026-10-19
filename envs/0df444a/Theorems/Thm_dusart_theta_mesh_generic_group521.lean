-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group521
-- name    : dusart_theta_mesh_generic_group521
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:13:16.463445+00:00
-- url     : https://prove2.me/theorems/e197ee62-23d3-4410-92dd-cfdafe0b74e9
-- title:
--   Verified numerical interval from 7129653504 to 7146430720
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7129653504, 7146430720; 7129598440326867, 7146367101927397).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group521 : DusartNumeric.GenericSpec 7129653504 7146430720 7129598440326867 7146367101927397 := by sorry
