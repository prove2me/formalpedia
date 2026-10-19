-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group477
-- name    : dusart_theta_mesh_generic_group477
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:20.504297+00:00
-- url     : https://prove2.me/theorems/6c5cba40-0524-4c61-9b54-dea79fa35154
-- title:
--   Verified numerical interval from 6391456000 to 6408233216
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6391456000, 6408233216; 6391395860310568, 6408166619468665).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group477 : DusartNumeric.GenericSpec 6391456000 6408233216 6391395860310568 6408166619468665 := by sorry
