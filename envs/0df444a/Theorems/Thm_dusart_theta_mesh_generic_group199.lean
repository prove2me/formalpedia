-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group199
-- name    : dusart_theta_mesh_generic_group199
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:13.394519+00:00
-- url     : https://prove2.me/theorems/2fb68fd1-9cb6-4309-9192-51063989e20b
-- title:
--   Verified numerical interval from 1727389952 to 1744167168
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1727389952, 1744167168; 1727361722337772, 1744130242829047).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group199 : DusartNumeric.GenericSpec 1727389952 1744167168 1727361722337772 1744130242829047 := by sorry
