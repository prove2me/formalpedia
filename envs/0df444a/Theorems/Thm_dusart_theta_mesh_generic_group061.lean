-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group061
-- name    : dusart_theta_mesh_generic_group061
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:14:04.597986+00:00
-- url     : https://prove2.me/theorems/bc9b869a-7e9f-4b38-913f-17f7b59507a5
-- title:
--   Verified numerical interval from 255189248 to 259383552
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(255189248, 259383552; 255177599586748, 259372293517085).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group061 : DusartNumeric.GenericSpec 255189248 259383552 255177599586748 259372293517085 := by sorry
