-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group432
-- name    : dusart_theta_mesh_generic_group432
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:02:38.637961+00:00
-- url     : https://prove2.me/theorems/0284942a-8265-481f-ad40-af1d26ffe41c
-- title:
--   Verified numerical interval from 5636481280 to 5653258496
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5636481280, 5653258496; 5636414126703903, 5653194244598227).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group432 : DusartNumeric.GenericSpec 5636481280 5653258496 5636414126703903 5653194244598227 := by sorry
