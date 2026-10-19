-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group099
-- name    : dusart_theta_mesh_generic_group099
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:26:21.752666+00:00
-- url     : https://prove2.me/theorems/3f5d5e0f-60d7-4c35-8e31-4fdfb9ffc14b
-- title:
--   Verified numerical interval from 427155712 to 435544320
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(427155712, 435544320; 427138220410921, 435523149688470).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group099 : DusartNumeric.GenericSpec 427155712 435544320 427138220410921 435523149688470 := by sorry
