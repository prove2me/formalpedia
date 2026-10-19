-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group594
-- name    : dusart_theta_mesh_generic_group594
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:21:22.435975+00:00
-- url     : https://prove2.me/theorems/fa9db4f1-2d86-4602-afda-0483892a5a70
-- title:
--   Verified numerical interval from 8354390272 to 8371167488
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8354390272, 8371167488; 8354319595350699, 8371109470543241).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group594 : DusartNumeric.GenericSpec 8354390272 8371167488 8354319595350699 8371109470543241 := by sorry
