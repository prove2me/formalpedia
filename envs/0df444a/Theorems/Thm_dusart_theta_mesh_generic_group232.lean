-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group232
-- name    : dusart_theta_mesh_generic_group232
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:40:25.55599+00:00
-- url     : https://prove2.me/theorems/2e2a5f04-07f4-47b1-8134-b13b4bd7678f
-- title:
--   Verified numerical interval from 2281038080 to 2297815296
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2281038080, 2297815296; 2281006415695123, 2297787624614847).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group232 : DusartNumeric.GenericSpec 2281038080 2297815296 2281006415695123 2297787624614847 := by sorry
