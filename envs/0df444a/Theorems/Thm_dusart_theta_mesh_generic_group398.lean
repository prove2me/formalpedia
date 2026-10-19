-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group398
-- name    : dusart_theta_mesh_generic_group398
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:58:59.152984+00:00
-- url     : https://prove2.me/theorems/0d567803-4939-4569-9085-ed18864ea3bc
-- title:
--   Verified numerical interval from 5066055936 to 5082833152
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5066055936, 5082833152; 5065976792211071, 5082756276075741).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group398 : DusartNumeric.GenericSpec 5066055936 5082833152 5065976792211071 5082756276075741 := by sorry
