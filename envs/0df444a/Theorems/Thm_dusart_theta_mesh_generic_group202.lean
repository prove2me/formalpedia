-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group202
-- name    : dusart_theta_mesh_generic_group202
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:35:12.058473+00:00
-- url     : https://prove2.me/theorems/3c2bb123-4be1-41e8-92e7-a6bc11f8d2de
-- title:
--   Verified numerical interval from 1777721600 to 1794498816
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1777721600, 1794498816; 1777681838997207, 1794465260341457).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group202 : DusartNumeric.GenericSpec 1777721600 1794498816 1777681838997207 1794465260341457 := by sorry
