-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group395
-- name    : dusart_theta_mesh_generic_group395
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:58:53.557315+00:00
-- url     : https://prove2.me/theorems/aac46131-f4dc-4b09-acf8-5ca5e891c294
-- title:
--   Verified numerical interval from 5015724288 to 5032501504
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5015724288, 5032501504; 5015654636552506, 5032441043214352).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group395 : DusartNumeric.GenericSpec 5015724288 5032501504 5015654636552506 5032441043214352 := by sorry
