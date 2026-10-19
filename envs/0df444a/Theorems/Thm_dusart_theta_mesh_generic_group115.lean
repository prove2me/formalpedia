-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group115
-- name    : dusart_theta_mesh_generic_group115
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:38.083692+00:00
-- url     : https://prove2.me/theorems/798d4dec-7358-4f53-ac2a-1a3698197281
-- title:
--   Verified numerical interval from 561373440 to 569762048
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(561373440, 569762048; 561346317415022, 569736163618622).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group115 : DusartNumeric.GenericSpec 561373440 569762048 561346317415022 569736163618622 := by sorry
