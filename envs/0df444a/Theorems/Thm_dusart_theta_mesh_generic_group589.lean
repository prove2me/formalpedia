-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group589
-- name    : dusart_theta_mesh_generic_group589
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:21:42.973986+00:00
-- url     : https://prove2.me/theorems/23cf7eb0-ccb2-43b0-a8ba-477d426546c5
-- title:
--   Verified numerical interval from 8270504192 to 8287281408
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8270504192, 8287281408; 8270429765431582, 8287225477379715).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group589 : DusartNumeric.GenericSpec 8270504192 8287281408 8270429765431582 8287225477379715 := by sorry
