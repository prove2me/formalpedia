-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group108
-- name    : dusart_theta_mesh_generic_group108
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:32.286964+00:00
-- url     : https://prove2.me/theorems/e6900d0f-5b49-47e2-ad08-cd4b0d018b25
-- title:
--   Verified numerical interval from 502653184 to 511041792
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(502653184, 511041792; 502634065851743, 511011810400810).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group108 : DusartNumeric.GenericSpec 502653184 511041792 502634065851743 511011810400810 := by sorry
