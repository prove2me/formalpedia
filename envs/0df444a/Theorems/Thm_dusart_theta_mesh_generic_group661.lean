-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group661
-- name    : dusart_theta_mesh_generic_group661
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:30:13.363986+00:00
-- url     : https://prove2.me/theorems/d0ecc3d2-1cfe-4452-b9ba-18d628f70f20
-- title:
--   Verified numerical interval from 9478463744 to 9495240960
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9478463744, 9495240960; 9478373058441958, 9495154464216269).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group661 : DusartNumeric.GenericSpec 9478463744 9495240960 9478373058441958 9495154464216269 := by sorry
