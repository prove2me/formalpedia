-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group651
-- name    : dusart_theta_mesh_generic_group651
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:28:36.127985+00:00
-- url     : https://prove2.me/theorems/edb607c6-d926-4315-8d10-075b1bb0169e
-- title:
--   Verified numerical interval from 9310691584 to 9327468800
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9310691584, 9327468800; 9310611837024355, 9327393591579001).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group651 : DusartNumeric.GenericSpec 9310691584 9327468800 9310611837024355 9327393591579001 := by sorry
