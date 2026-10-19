-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group203
-- name    : dusart_theta_mesh_generic_group203
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:35:27.185325+00:00
-- url     : https://prove2.me/theorems/b35eab8a-20ad-47b7-932a-773b617a7969
-- title:
--   Verified numerical interval from 1794498816 to 1811276032
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1794498816, 1811276032; 1794465260341457, 1811247136805645).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group203 : DusartNumeric.GenericSpec 1794498816 1811276032 1794465260341457 1811247136805645 := by sorry
