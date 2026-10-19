-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group511
-- name    : dusart_theta_mesh_generic_group511
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:11:19.699971+00:00
-- url     : https://prove2.me/theorems/e43f1acd-8b20-4e8c-942f-01e304c63a07
-- title:
--   Verified numerical interval from 6961881344 to 6978658560
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6961881344, 6978658560; 6961794975462764, 6978574684952288).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group511 : DusartNumeric.GenericSpec 6961881344 6978658560 6961794975462764 6978574684952288 := by sorry
