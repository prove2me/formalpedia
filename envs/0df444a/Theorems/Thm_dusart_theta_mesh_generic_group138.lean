-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group138
-- name    : dusart_theta_mesh_generic_group138
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:29:10.495023+00:00
-- url     : https://prove2.me/theorems/26ef1c04-31d0-46f0-8558-17d83a7820e9
-- title:
--   Verified numerical interval from 754311424 to 762700032
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(754311424, 762700032; 754274368879725, 762668836872636).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group138 : DusartNumeric.GenericSpec 754311424 762700032 754274368879725 762668836872636 := by sorry
