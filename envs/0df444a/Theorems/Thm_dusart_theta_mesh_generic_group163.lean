-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group163
-- name    : dusart_theta_mesh_generic_group163
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:30:59.789905+00:00
-- url     : https://prove2.me/theorems/b23ba4a2-8e47-4392-b738-0f5c8b8de8bf
-- title:
--   Verified numerical interval from 1123410176 to 1140187392
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1123410176, 1140187392; 1123398274708753, 1140158783179798).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group163 : DusartNumeric.GenericSpec 1123410176 1140187392 1123398274708753 1140158783179798 := by sorry
