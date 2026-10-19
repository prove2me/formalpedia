-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group064
-- name    : dusart_theta_mesh_generic_group064
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:14:47.125023+00:00
-- url     : https://prove2.me/theorems/6f76d26a-2d37-49b7-95d1-9f2433ec336f
-- title:
--   Verified numerical interval from 267772160 to 271966464
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(267772160, 271966464; 267757896932078, 271948915868079).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group064 : DusartNumeric.GenericSpec 267772160 271966464 267757896932078 271948915868079 := by sorry
