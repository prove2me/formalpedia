-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group230
-- name    : dusart_theta_mesh_generic_group230
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:40:00.641129+00:00
-- url     : https://prove2.me/theorems/140eb947-8b6b-4d2b-9c98-dd8bd3409760
-- title:
--   Verified numerical interval from 2247483648 to 2264260864
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2247483648, 2264260864; 2247432638541906, 2264215531732664).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group230 : DusartNumeric.GenericSpec 2247483648 2264260864 2247432638541906 2264215531732664 := by sorry
