-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group159
-- name    : dusart_theta_mesh_generic_group159
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:30:54.65596+00:00
-- url     : https://prove2.me/theorems/66f1176f-df9f-41bb-8eac-2a90a6096b1d
-- title:
--   Verified numerical interval from 1056301312 to 1073078528
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1056301312, 1073078528; 1056269876044605, 1073057150451995).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group159 : DusartNumeric.GenericSpec 1056301312 1073078528 1056269876044605 1073057150451995 := by sorry
