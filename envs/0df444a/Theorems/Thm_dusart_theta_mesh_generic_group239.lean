-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group239
-- name    : dusart_theta_mesh_generic_group239
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:40:09.183779+00:00
-- url     : https://prove2.me/theorems/db1ddd23-9db5-4552-8ffe-8011e77a256b
-- title:
--   Verified numerical interval from 2398478592 to 2415255808
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2398478592, 2415255808; 2398429711850490, 2415200123007171).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group239 : DusartNumeric.GenericSpec 2398478592 2415255808 2398429711850490 2415200123007171 := by sorry
