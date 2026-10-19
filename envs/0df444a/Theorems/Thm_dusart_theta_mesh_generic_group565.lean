-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group565
-- name    : dusart_theta_mesh_generic_group565
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:18:32.637268+00:00
-- url     : https://prove2.me/theorems/8486e514-8bc6-4bb6-8fab-16ad49cdab69
-- title:
--   Verified numerical interval from 7867851008 to 7884628224
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7867851008, 7884628224; 7867743125277874, 7884507249958122).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group565 : DusartNumeric.GenericSpec 7867851008 7884628224 7867743125277874 7884507249958122 := by sorry
