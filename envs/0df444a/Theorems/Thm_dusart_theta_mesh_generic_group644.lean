-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group644
-- name    : dusart_theta_mesh_generic_group644
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:28:43.354647+00:00
-- url     : https://prove2.me/theorems/503e7ade-7efa-488d-9ed3-a56f00b48e94
-- title:
--   Verified numerical interval from 9193251072 to 9210028288
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9193251072, 9210028288; 9193124440125327, 9209916104016494).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group644 : DusartNumeric.GenericSpec 9193251072 9210028288 9193124440125327 9209916104016494 := by sorry
