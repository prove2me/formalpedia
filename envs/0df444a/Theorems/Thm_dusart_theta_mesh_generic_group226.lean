-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group226
-- name    : dusart_theta_mesh_generic_group226
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:39:24.003375+00:00
-- url     : https://prove2.me/theorems/aa2b6922-9f97-4609-8955-e99cb29018c6
-- title:
--   Verified numerical interval from 2180374784 to 2197152000
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2180374784, 2197152000; 2180335408068253, 2197108016759433).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group226 : DusartNumeric.GenericSpec 2180374784 2197152000 2180335408068253 2197108016759433 := by sorry
