-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group112
-- name    : dusart_theta_mesh_generic_group112
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:38.632353+00:00
-- url     : https://prove2.me/theorems/23b7e1e8-e5e7-4c9f-91b0-cbd382a6d04d
-- title:
--   Verified numerical interval from 536207616 to 544596224
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(536207616, 544596224; 536181549944858, 544563465880650).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group112 : DusartNumeric.GenericSpec 536207616 544596224 536181549944858 544563465880650 := by sorry
