-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group114
-- name    : dusart_theta_mesh_generic_group114
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:38.717518+00:00
-- url     : https://prove2.me/theorems/96e1b646-c966-4627-9a7a-4dc34f339b12
-- title:
--   Verified numerical interval from 552984832 to 561373440
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(552984832, 561373440; 552963477152353, 561346317415022).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group114 : DusartNumeric.GenericSpec 552984832 561373440 552963477152353 561346317415022 := by sorry
