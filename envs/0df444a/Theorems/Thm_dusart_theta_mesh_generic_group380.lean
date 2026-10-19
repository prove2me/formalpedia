-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group380
-- name    : dusart_theta_mesh_generic_group380
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:56:01.55019+00:00
-- url     : https://prove2.me/theorems/25a387cb-9d80-417a-9afc-67e5541ca50f
-- title:
--   Verified numerical interval from 4764066048 to 4780843264
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4764066048, 4780843264; 4764027277976877, 4780778254784307).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group380 : DusartNumeric.GenericSpec 4764066048 4780843264 4764027277976877 4780778254784307 := by sorry
