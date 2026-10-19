-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group212
-- name    : dusart_theta_mesh_generic_group212
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:36:17.063145+00:00
-- url     : https://prove2.me/theorems/f031b8f8-0ddb-4f25-a58c-ed7e5c24a95f
-- title:
--   Verified numerical interval from 1945493760 to 1962270976
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1945493760, 1962270976; 1945437962943639, 1962220981220282).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group212 : DusartNumeric.GenericSpec 1945493760 1962270976 1945437962943639 1962220981220282 := by sorry
