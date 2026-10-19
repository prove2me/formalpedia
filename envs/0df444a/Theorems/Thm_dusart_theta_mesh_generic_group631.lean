-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group631
-- name    : dusart_theta_mesh_generic_group631
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:27:47.675322+00:00
-- url     : https://prove2.me/theorems/c6be6fce-8d39-49aa-acf3-bc0a0ffbfec7
-- title:
--   Verified numerical interval from 8975147264 to 8991924480
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8975147264, 8991924480; 8975048488146620, 8991830707884628).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group631 : DusartNumeric.GenericSpec 8975147264 8991924480 8975048488146620 8991830707884628 := by sorry
