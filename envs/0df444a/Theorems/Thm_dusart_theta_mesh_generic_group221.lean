-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group221
-- name    : dusart_theta_mesh_generic_group221
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:37:43.226679+00:00
-- url     : https://prove2.me/theorems/758d68fa-0653-4a34-9210-57db4cbf8b70
-- title:
--   Verified numerical interval from 2096488704 to 2113265920
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2096488704, 2113265920; 2096445430583416, 2113235110363146).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group221 : DusartNumeric.GenericSpec 2096488704 2113265920 2096445430583416 2113235110363146 := by sorry
