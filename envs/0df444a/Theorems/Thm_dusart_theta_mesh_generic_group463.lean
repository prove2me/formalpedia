-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group463
-- name    : dusart_theta_mesh_generic_group463
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:11.164021+00:00
-- url     : https://prove2.me/theorems/a3cd21b7-6894-4a59-9e61-59416557daaa
-- title:
--   Verified numerical interval from 6156574976 to 6173352192
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6156574976, 6173352192; 6156516838438961, 6173297875971162).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group463 : DusartNumeric.GenericSpec 6156574976 6173352192 6156516838438961 6173297875971162 := by sorry
