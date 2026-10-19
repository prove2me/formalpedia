-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group375
-- name    : dusart_theta_mesh_generic_group375
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:56:09.092933+00:00
-- url     : https://prove2.me/theorems/6c6af1c5-b9e2-4c0c-8e1c-6a3bab6b196e
-- title:
--   Verified numerical interval from 4680179968 to 4696957184
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4680179968, 4696957184; 4680117199521150, 4696904906644585).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group375 : DusartNumeric.GenericSpec 4680179968 4696957184 4680117199521150 4696904906644585 := by sorry
