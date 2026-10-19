-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group492
-- name    : dusart_theta_mesh_generic_group492
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:10:31.07558+00:00
-- url     : https://prove2.me/theorems/dc53287f-9833-40d9-ac0c-1b91c536ec10
-- title:
--   Verified numerical interval from 6643114240 to 6659891456
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6643114240, 6659891456; 6643063840907749, 6659837100005641).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group492 : DusartNumeric.GenericSpec 6643114240 6659891456 6643063840907749 6659837100005641 := by sorry
