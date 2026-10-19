-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group643
-- name    : dusart_theta_mesh_generic_group643
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:32:01.553176+00:00
-- url     : https://prove2.me/theorems/4b5ff80e-8cb9-44e1-bf0b-b5a23b75b364
-- title:
--   Verified numerical interval from 9176473856 to 9193251072
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9176473856, 9193251072; 9176361435348381, 9193124440125327).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group643 : DusartNumeric.GenericSpec 9176473856 9193251072 9176361435348381 9193124440125327 := by sorry
