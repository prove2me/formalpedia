-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group044
-- name    : dusart_theta_mesh_generic_group044
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:12:57.793336+00:00
-- url     : https://prove2.me/theorems/419239e3-8d8c-4f43-b394-ac9745abe42d
-- title:
--   Verified numerical interval from 192274688 to 194371840
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(192274688, 194371840; 192260420795188, 194361670652736).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group044 : DusartNumeric.GenericSpec 192274688 194371840 192260420795188 194361670652736 := by sorry
