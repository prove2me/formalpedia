-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group020
-- name    : dusart_theta_mesh_generic_group020
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:10:49.9853+00:00
-- url     : https://prove2.me/theorems/e6c0a06c-00a9-47b4-b7a7-1df279b580e9
-- title:
--   Verified numerical interval from 141943040 to 144040192
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(141943040, 144040192; 141928752422099, 144031811556532).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group020 : DusartNumeric.GenericSpec 141943040 144040192 141928752422099 144031811556532 := by sorry
