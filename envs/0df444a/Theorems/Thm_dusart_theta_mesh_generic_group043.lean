-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group043
-- name    : dusart_theta_mesh_generic_group043
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:12:46.569444+00:00
-- url     : https://prove2.me/theorems/193f810f-11d7-4208-a0d1-97b740b6b8b4
-- title:
--   Verified numerical interval from 190177536 to 192274688
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(190177536, 192274688; 190170078116059, 192260420795188).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group043 : DusartNumeric.GenericSpec 190177536 192274688 190170078116059 192260420795188 := by sorry
