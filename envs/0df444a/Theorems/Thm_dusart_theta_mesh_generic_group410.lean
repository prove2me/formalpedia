-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group410
-- name    : dusart_theta_mesh_generic_group410
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:59:29.783852+00:00
-- url     : https://prove2.me/theorems/d857764a-ad25-42e5-86b5-54b7708e84cc
-- title:
--   Verified numerical interval from 5267382528 to 5284159744
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5267382528, 5284159744; 5267313562107754, 5284093851512139).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group410 : DusartNumeric.GenericSpec 5267382528 5284159744 5267313562107754 5284093851512139 := by sorry
