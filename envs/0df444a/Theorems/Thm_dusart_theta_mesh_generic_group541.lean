-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group541
-- name    : dusart_theta_mesh_generic_group541
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:14:30.433468+00:00
-- url     : https://prove2.me/theorems/2a5d1864-db2f-4b1c-8313-39a165bb3a2a
-- title:
--   Verified numerical interval from 7465197824 to 7481975040
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7465197824, 7481975040; 7465120401160175, 7481892140071271).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group541 : DusartNumeric.GenericSpec 7465197824 7481975040 7465120401160175 7481892140071271 := by sorry
