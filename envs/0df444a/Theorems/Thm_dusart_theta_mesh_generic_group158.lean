-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group158
-- name    : dusart_theta_mesh_generic_group158
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:30:52.230426+00:00
-- url     : https://prove2.me/theorems/75f0a064-d80f-4838-9d98-5ffa3a71b4ef
-- title:
--   Verified numerical interval from 1039524096 to 1056301312
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1039524096, 1056301312; 1039500314169685, 1056269876044605).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group158 : DusartNumeric.GenericSpec 1039524096 1056301312 1039500314169685 1056269876044605 := by sorry
