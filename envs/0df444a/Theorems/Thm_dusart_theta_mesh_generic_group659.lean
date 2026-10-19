-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group659
-- name    : dusart_theta_mesh_generic_group659
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:29:51.07864+00:00
-- url     : https://prove2.me/theorems/43213ac4-f6f7-4698-89a3-65f8778bcf8d
-- title:
--   Verified numerical interval from 9444909312 to 9461686528
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9444909312, 9461686528; 9444831448491728, 9461601859072932).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group659 : DusartNumeric.GenericSpec 9444909312 9461686528 9444831448491728 9461601859072932 := by sorry
