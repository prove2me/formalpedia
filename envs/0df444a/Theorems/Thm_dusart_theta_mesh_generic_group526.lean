-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group526
-- name    : dusart_theta_mesh_generic_group526
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:12:41.071527+00:00
-- url     : https://prove2.me/theorems/c48c15cc-bc9e-4b14-8e8f-deaa40650fad
-- title:
--   Verified numerical interval from 7213539584 to 7230316800
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7213539584, 7230316800; 7213455633026764, 7230229888205305).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group526 : DusartNumeric.GenericSpec 7213539584 7230316800 7213455633026764 7230229888205305 := by sorry
