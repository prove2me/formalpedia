-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group340
-- name    : dusart_theta_mesh_generic_group340
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:33.720886+00:00
-- url     : https://prove2.me/theorems/96715eda-8d46-4abe-a83b-5948b45f4cd3
-- title:
--   Verified numerical interval from 4092977408 to 4109754624
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4092977408, 4109754624; 4092908469329160, 4109684349184503).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group340 : DusartNumeric.GenericSpec 4092977408 4109754624 4092908469329160 4109684349184503 := by sorry
