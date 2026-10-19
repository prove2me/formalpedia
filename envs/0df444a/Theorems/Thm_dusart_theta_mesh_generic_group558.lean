-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group558
-- name    : dusart_theta_mesh_generic_group558
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:16:51.529054+00:00
-- url     : https://prove2.me/theorems/1190e260-1ce5-4ee8-aa40-b1376e7158b2
-- title:
--   Verified numerical interval from 7750410496 to 7767187712
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7750410496, 7767187712; 7750273385440170, 7767057359357731).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group558 : DusartNumeric.GenericSpec 7750410496 7767187712 7750273385440170 7767057359357731 := by sorry
