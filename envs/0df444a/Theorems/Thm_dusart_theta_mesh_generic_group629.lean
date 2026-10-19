-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group629
-- name    : dusart_theta_mesh_generic_group629
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:25:42.437238+00:00
-- url     : https://prove2.me/theorems/3531d76e-a6be-4545-99c6-59f4db539795
-- title:
--   Verified numerical interval from 8941592832 to 8958370048
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8941592832, 8958370048; 8941493543437037, 8958280149507488).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group629 : DusartNumeric.GenericSpec 8941592832 8958370048 8941493543437037 8958280149507488 := by sorry
