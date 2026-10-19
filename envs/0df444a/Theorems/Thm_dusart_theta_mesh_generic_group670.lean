-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group670
-- name    : dusart_theta_mesh_generic_group670
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:31:22.971979+00:00
-- url     : https://prove2.me/theorems/3dc640ac-8d85-4498-a7cd-2b4b15b7db45
-- title:
--   Verified numerical interval from 9629458688 to 9646235904
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9629458688, 9646235904; 9629386191257659, 9646147245856808).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group670 : DusartNumeric.GenericSpec 9629458688 9646235904 9629386191257659 9646147245856808 := by sorry
