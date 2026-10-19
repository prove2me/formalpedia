-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group173
-- name    : dusart_theta_mesh_generic_group173
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:33:06.655273+00:00
-- url     : https://prove2.me/theorems/e77720bd-3d4a-47a7-8965-41c14b003e21
-- title:
--   Verified numerical interval from 1291182336 to 1307959552
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1291182336, 1307959552; 1291149351573464, 1307919231119769).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group173 : DusartNumeric.GenericSpec 1291182336 1307959552 1291149351573464 1307919231119769 := by sorry
