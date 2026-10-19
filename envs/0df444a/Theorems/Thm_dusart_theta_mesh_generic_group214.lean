-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group214
-- name    : dusart_theta_mesh_generic_group214
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:37:36.282359+00:00
-- url     : https://prove2.me/theorems/0114b83d-e349-4d16-bf89-eade20e38aa1
-- title:
--   Verified numerical interval from 1979048192 to 1995825408
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1979048192, 1995825408; 1979001356112509, 1995777328891693).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group214 : DusartNumeric.GenericSpec 1979048192 1995825408 1979001356112509 1995777328891693 := by sorry
