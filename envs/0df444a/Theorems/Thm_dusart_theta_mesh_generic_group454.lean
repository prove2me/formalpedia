-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group454
-- name    : dusart_theta_mesh_generic_group454
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:04:09.599992+00:00
-- url     : https://prove2.me/theorems/8b22d04d-f35a-4fbf-8622-f0303408ad65
-- title:
--   Verified numerical interval from 6005580032 to 6022357248
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6005580032, 6022357248; 6005513544703345, 6022288800016644).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group454 : DusartNumeric.GenericSpec 6005580032 6022357248 6005513544703345 6022288800016644 := by sorry
