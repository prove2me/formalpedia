-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group220
-- name    : dusart_theta_mesh_generic_group220
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:38:51.107139+00:00
-- url     : https://prove2.me/theorems/1c4eab34-d5b3-46d7-a031-4d820ed9619c
-- title:
--   Verified numerical interval from 2079711488 to 2096488704
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2079711488, 2096488704; 2079664521041153, 2096445430583416).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group220 : DusartNumeric.GenericSpec 2079711488 2096488704 2079664521041153 2096445430583416 := by sorry
