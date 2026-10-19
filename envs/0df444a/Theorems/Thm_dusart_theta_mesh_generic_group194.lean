-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group194
-- name    : dusart_theta_mesh_generic_group194
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:12.847191+00:00
-- url     : https://prove2.me/theorems/18ad77be-7703-41fd-b8bb-6369fa8a9387
-- title:
--   Verified numerical interval from 1643503872 to 1660281088
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1643503872, 1660281088; 1643480000053453, 1660238725895404).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group194 : DusartNumeric.GenericSpec 1643503872 1660281088 1643480000053453 1660238725895404 := by sorry
