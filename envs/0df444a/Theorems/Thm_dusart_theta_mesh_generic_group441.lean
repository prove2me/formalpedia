-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group441
-- name    : dusart_theta_mesh_generic_group441
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:02:56.417028+00:00
-- url     : https://prove2.me/theorems/5b7562d8-a313-45a8-9f05-ba0ff1951ed0
-- title:
--   Verified numerical interval from 5787476224 to 5804253440
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5787476224, 5804253440; 5787412052161762, 5804192811476465).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group441 : DusartNumeric.GenericSpec 5787476224 5804253440 5787412052161762 5804192811476465 := by sorry
