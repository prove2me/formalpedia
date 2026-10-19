-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group088
-- name    : dusart_theta_mesh_generic_group088
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:26:00.598065+00:00
-- url     : https://prove2.me/theorems/8cd779f7-76a0-4352-829c-5fc9e18a7b10
-- title:
--   Verified numerical interval from 368435456 to 372629760
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(368435456, 372629760; 368414392930268, 372602778371437).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group088 : DusartNumeric.GenericSpec 368435456 372629760 368414392930268 372602778371437 := by sorry
