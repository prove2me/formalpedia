-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group632
-- name    : dusart_theta_mesh_generic_group632
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:25:58.150993+00:00
-- url     : https://prove2.me/theorems/71a1b3e3-8347-482a-a8dd-8e95db213d86
-- title:
--   Verified numerical interval from 8991924480 to 9008701696
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8991924480, 9008701696; 8991830707884628, 9008609251355623).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group632 : DusartNumeric.GenericSpec 8991924480 9008701696 8991830707884628 9008609251355623 := by sorry
