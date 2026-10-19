-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group345
-- name    : dusart_theta_mesh_generic_group345
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:52.110117+00:00
-- url     : https://prove2.me/theorems/b0519c8e-7a5a-4d1b-b037-7c0f112e425a
-- title:
--   Verified numerical interval from 4176863488 to 4193640704
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4176863488, 4193640704; 4176784941689640, 4193556514416307).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group345 : DusartNumeric.GenericSpec 4176863488 4193640704 4176784941689640 4193556514416307 := by sorry
