-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group079
-- name    : dusart_theta_mesh_generic_group079
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:24:50.848063+00:00
-- url     : https://prove2.me/theorems/0e09a5c4-e084-48ea-855f-635d15d97353
-- title:
--   Verified numerical interval from 330686720 to 334881024
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(330686720, 334881024; 330666970911260, 334862277062422).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group079 : DusartNumeric.GenericSpec 330686720 334881024 330666970911260 334862277062422 := by sorry
