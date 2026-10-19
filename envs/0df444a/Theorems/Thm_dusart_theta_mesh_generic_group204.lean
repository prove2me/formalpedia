-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group204
-- name    : dusart_theta_mesh_generic_group204
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:36:23.092793+00:00
-- url     : https://prove2.me/theorems/da7fffac-2eb2-4d79-8d93-08c79d55610a
-- title:
--   Verified numerical interval from 1811276032 to 1828053248
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1811276032, 1828053248; 1811247136805645, 1828018271155455).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group204 : DusartNumeric.GenericSpec 1811276032 1828053248 1811247136805645 1828018271155455 := by sorry
