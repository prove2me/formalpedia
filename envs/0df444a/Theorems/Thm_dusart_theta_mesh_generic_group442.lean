-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group442
-- name    : dusart_theta_mesh_generic_group442
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:03:00.48997+00:00
-- url     : https://prove2.me/theorems/696e6f22-afa0-4eb1-85ef-c940e5fd52f3
-- title:
--   Verified numerical interval from 5804253440 to 5821030656
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5804253440, 5821030656; 5804192811476465, 5820967656865890).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group442 : DusartNumeric.GenericSpec 5804253440 5821030656 5804192811476465 5820967656865890 := by sorry
