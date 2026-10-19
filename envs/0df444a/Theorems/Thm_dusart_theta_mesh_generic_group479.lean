-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group479
-- name    : dusart_theta_mesh_generic_group479
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:08:14.833956+00:00
-- url     : https://prove2.me/theorems/470dd217-07b8-4447-850a-189285f8b8de
-- title:
--   Verified numerical interval from 6425010432 to 6441787648
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6425010432, 6441787648; 6424931215671588, 6441698088936622).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group479 : DusartNumeric.GenericSpec 6425010432 6441787648 6424931215671588 6441698088936622 := by sorry
