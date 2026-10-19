-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group532
-- name    : dusart_theta_mesh_generic_group532
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:16:38.797009+00:00
-- url     : https://prove2.me/theorems/e2eaa9f8-3dd3-4aba-ae9e-7e5120aa8624
-- title:
--   Verified numerical interval from 7314202880 to 7330980096
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7314202880, 7330980096; 7314096442054323, 7330894418624991).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group532 : DusartNumeric.GenericSpec 7314202880 7330980096 7314096442054323 7330894418624991 := by sorry
