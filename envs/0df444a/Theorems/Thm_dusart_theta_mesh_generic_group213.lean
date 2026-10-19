-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group213
-- name    : dusart_theta_mesh_generic_group213
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:36:58.444042+00:00
-- url     : https://prove2.me/theorems/47c4ee0b-5e1b-4098-81cd-e2b9b216b826
-- title:
--   Verified numerical interval from 1962270976 to 1979048192
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1962270976, 1979048192; 1962220981220282, 1979001356112509).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group213 : DusartNumeric.GenericSpec 1962270976 1979048192 1962220981220282 1979001356112509 := by sorry
