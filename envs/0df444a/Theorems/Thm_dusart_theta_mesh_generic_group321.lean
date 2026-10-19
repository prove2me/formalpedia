-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group321
-- name    : dusart_theta_mesh_generic_group321
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:48:51.54803+00:00
-- url     : https://prove2.me/theorems/1b16b662-8e1a-40aa-82cd-09377da2ed1a
-- title:
--   Verified numerical interval from 3774210304 to 3790987520
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3774210304, 3790987520; 3774185101143134, 3790956007525928).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group321 : DusartNumeric.GenericSpec 3774210304 3790987520 3774185101143134 3790956007525928 := by sorry
