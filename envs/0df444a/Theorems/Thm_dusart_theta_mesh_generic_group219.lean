-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group219
-- name    : dusart_theta_mesh_generic_group219
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:38:25.799666+00:00
-- url     : https://prove2.me/theorems/821717ef-b60a-453b-a164-6eb923835baa
-- title:
--   Verified numerical interval from 2062934272 to 2079711488
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2062934272, 2079711488; 2062887667533560, 2079664521041153).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group219 : DusartNumeric.GenericSpec 2062934272 2079711488 2062887667533560 2079664521041153 := by sorry
