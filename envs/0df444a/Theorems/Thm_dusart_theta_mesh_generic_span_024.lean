-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_span_024
-- name    : dusart_theta_mesh_generic_span_024
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T00:46:57.294103+00:00
-- url     : https://prove2.me/theorems/5f49f347-0b32-4572-8a13-7daca33bc845
-- title:
--   Verified numerical interval from 1609949440 to 1744167168
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and that is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1609949440, 1744167168; 1609919129810472, 1744130242829047).$$
--
--   The final two arguments are endpoint carries with fixed scale one million. This result makes the verified numerical interval available as an independent input to the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_span_024 : DusartNumeric.GenericSpec 1609949440 1744167168 1609919129810472 1744130242829047 := by sorry
