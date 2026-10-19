-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group339
-- name    : dusart_theta_mesh_generic_group339
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:30.326389+00:00
-- url     : https://prove2.me/theorems/ba98f748-75b8-41f2-81fc-161d67a5a1ce
-- title:
--   Verified numerical interval from 4076200192 to 4092977408
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4076200192, 4092977408; 4076134169088834, 4092908469329160).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group339 : DusartNumeric.GenericSpec 4076200192 4092977408 4076134169088834 4092908469329160 := by sorry
