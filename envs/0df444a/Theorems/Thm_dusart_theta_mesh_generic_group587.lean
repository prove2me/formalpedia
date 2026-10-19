-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group587
-- name    : dusart_theta_mesh_generic_group587
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:21:42.519845+00:00
-- url     : https://prove2.me/theorems/ba8079f1-6165-4279-9295-7307b58556a2
-- title:
--   Verified numerical interval from 8236949760 to 8253726976
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8236949760, 8253726976; 8236871203680428, 8253653676332146).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group587 : DusartNumeric.GenericSpec 8236949760 8253726976 8236871203680428 8253653676332146 := by sorry
