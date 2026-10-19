-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group590
-- name    : dusart_theta_mesh_generic_group590
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:20:50.71352+00:00
-- url     : https://prove2.me/theorems/68aab28c-9580-49de-97a8-c95b346bdd42
-- title:
--   Verified numerical interval from 8287281408 to 8304058624
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8287281408, 8304058624; 8287225477379715, 8304000844650275).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group590 : DusartNumeric.GenericSpec 8287281408 8304058624 8287225477379715 8304000844650275 := by sorry
