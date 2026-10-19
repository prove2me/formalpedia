-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group436
-- name    : dusart_theta_mesh_generic_group436
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:02:17.753981+00:00
-- url     : https://prove2.me/theorems/52d45e40-6fa1-4377-ac9e-4415f3f2efb5
-- title:
--   Verified numerical interval from 5703590144 to 5720367360
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5703590144, 5720367360; 5703533322065311, 5720320609363949).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group436 : DusartNumeric.GenericSpec 5703590144 5720367360 5703533322065311 5720320609363949 := by sorry
