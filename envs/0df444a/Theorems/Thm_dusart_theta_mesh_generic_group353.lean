-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group353
-- name    : dusart_theta_mesh_generic_group353
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:53:05.551986+00:00
-- url     : https://prove2.me/theorems/27e4bab8-c7ea-4e2a-8bb0-711dd12b38ac
-- title:
--   Verified numerical interval from 4311081216 to 4327858432
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4311081216, 4327858432; 4311003407231951, 4327783569067626).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group353 : DusartNumeric.GenericSpec 4311081216 4327858432 4311003407231951 4327783569067626 := by sorry
