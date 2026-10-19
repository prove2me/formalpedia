-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group379
-- name    : dusart_theta_mesh_generic_group379
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:58:13.778813+00:00
-- url     : https://prove2.me/theorems/ceaa3e62-d9ab-452f-8d97-5584ad81102d
-- title:
--   Verified numerical interval from 4747288832 to 4764066048
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4747288832, 4764066048; 4747234539669818, 4764027277976877).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group379 : DusartNumeric.GenericSpec 4747288832 4764066048 4747234539669818 4764027277976877 := by sorry
