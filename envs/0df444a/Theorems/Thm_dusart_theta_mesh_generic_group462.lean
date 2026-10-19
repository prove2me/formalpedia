-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group462
-- name    : dusart_theta_mesh_generic_group462
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:08:13.430741+00:00
-- url     : https://prove2.me/theorems/d827f23a-8433-47bc-b2fa-ec86d6d17fef
-- title:
--   Verified numerical interval from 6139797760 to 6156574976
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6139797760, 6156574976; 6139742675747111, 6156516838438961).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group462 : DusartNumeric.GenericSpec 6139797760 6156574976 6139742675747111 6156516838438961 := by sorry
