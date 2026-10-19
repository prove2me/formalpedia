-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group292
-- name    : dusart_theta_mesh_generic_group292
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:47:46.053983+00:00
-- url     : https://prove2.me/theorems/e961d46a-460b-4b93-ac3e-c745d283d44e
-- title:
--   Verified numerical interval from 3287671040 to 3304448256
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3287671040, 3304448256; 3287602530678466, 3304376957655070).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group292 : DusartNumeric.GenericSpec 3287671040 3304448256 3287602530678466 3304376957655070 := by sorry
