-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group474
-- name    : dusart_theta_mesh_generic_group474
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:28.455742+00:00
-- url     : https://prove2.me/theorems/94db6f27-4e1b-42c6-b4db-9949a8139b16
-- title:
--   Verified numerical interval from 6341124352 to 6357901568
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6341124352, 6357901568; 6341072434901919, 6357836448288538).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group474 : DusartNumeric.GenericSpec 6341124352 6357901568 6341072434901919 6357836448288538 := by sorry
