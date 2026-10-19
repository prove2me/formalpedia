-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group630
-- name    : dusart_theta_mesh_generic_group630
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:26:03.01426+00:00
-- url     : https://prove2.me/theorems/bdd63a05-673b-42a6-9652-5f6092b917ee
-- title:
--   Verified numerical interval from 8958370048 to 8975147264
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8958370048, 8975147264; 8958280149507488, 8975048488146620).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group630 : DusartNumeric.GenericSpec 8958370048 8975147264 8958280149507488 8975048488146620 := by sorry
