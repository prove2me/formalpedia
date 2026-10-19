-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group031
-- name    : dusart_theta_mesh_generic_group031
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:48.873061+00:00
-- url     : https://prove2.me/theorems/62a76945-cb2c-4454-96c9-f6044af28b14
-- title:
--   Verified numerical interval from 165011712 to 167108864
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(165011712, 167108864; 164999456331067, 167094547216418).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group031 : DusartNumeric.GenericSpec 165011712 167108864 164999456331067 167094547216418 := by sorry
