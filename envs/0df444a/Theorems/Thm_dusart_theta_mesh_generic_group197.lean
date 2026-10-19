-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group197
-- name    : dusart_theta_mesh_generic_group197
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:14.033208+00:00
-- url     : https://prove2.me/theorems/5ca1ca93-57ac-491b-8780-a24dd78e8374
-- title:
--   Verified numerical interval from 1693835520 to 1710612736
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1693835520, 1710612736; 1693802801753479, 1710582910507471).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group197 : DusartNumeric.GenericSpec 1693835520 1710612736 1693802801753479 1710582910507471 := by sorry
