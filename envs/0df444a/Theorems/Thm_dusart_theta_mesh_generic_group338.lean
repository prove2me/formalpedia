-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group338
-- name    : dusart_theta_mesh_generic_group338
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:10.715985+00:00
-- url     : https://prove2.me/theorems/c2d71bdf-f3b7-4439-a319-79fadb14541f
-- title:
--   Verified numerical interval from 4059422976 to 4076200192
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4059422976, 4076200192; 4059363188859537, 4076134169088834).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group338 : DusartNumeric.GenericSpec 4059422976 4076200192 4059363188859537 4076134169088834 := by sorry
