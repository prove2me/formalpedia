-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group467
-- name    : dusart_theta_mesh_generic_group467
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:14.637572+00:00
-- url     : https://prove2.me/theorems/41023670-229f-413f-91d6-61c05bed8e2b
-- title:
--   Verified numerical interval from 6223683840 to 6240461056
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6223683840, 6240461056; 6223635651701983, 6240415750874133).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group467 : DusartNumeric.GenericSpec 6223683840 6240461056 6223635651701983 6240415750874133 := by sorry
