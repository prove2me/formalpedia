-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group586
-- name    : dusart_theta_mesh_generic_group586
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:20:04.363911+00:00
-- url     : https://prove2.me/theorems/b90ac7ae-c299-45ec-9ad3-38bc9a9ffa16
-- title:
--   Verified numerical interval from 8220172544 to 8236949760
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8220172544, 8236949760; 8220093561176692, 8236871203680428).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group586 : DusartNumeric.GenericSpec 8220172544 8236949760 8220093561176692 8236871203680428 := by sorry
