-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group344
-- name    : dusart_theta_mesh_generic_group344
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:54:54.051817+00:00
-- url     : https://prove2.me/theorems/3c1e7b68-e6fd-4af0-a813-d023520a47be
-- title:
--   Verified numerical interval from 4160086272 to 4176863488
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4160086272, 4176863488; 4160027440691635, 4176784941689640).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group344 : DusartNumeric.GenericSpec 4160086272 4176863488 4160027440691635 4176784941689640 := by sorry
