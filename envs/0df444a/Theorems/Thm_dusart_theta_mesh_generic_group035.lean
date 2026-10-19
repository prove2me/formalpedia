-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group035
-- name    : dusart_theta_mesh_generic_group035
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:12:45.02901+00:00
-- url     : https://prove2.me/theorems/2b6d5250-5b15-4b32-bdfc-11b9e7fd9678
-- title:
--   Verified numerical interval from 173400320 to 175497472
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(173400320, 175497472; 173391852119864, 175490025176949).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group035 : DusartNumeric.GenericSpec 173400320 175497472 173391852119864 175490025176949 := by sorry
