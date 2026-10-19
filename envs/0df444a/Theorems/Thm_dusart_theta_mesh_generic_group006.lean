-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group006
-- name    : dusart_theta_mesh_generic_group006
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:15.151196+00:00
-- url     : https://prove2.me/theorems/a6194b4b-88dd-4c3a-a82f-132d34278b40
-- title:
--   Verified numerical interval from 112582912 to 114680064
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(112582912, 114680064; 112576881613652, 114671748283717).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group006 : DusartNumeric.GenericSpec 112582912 114680064 112576881613652 114671748283717 := by sorry
