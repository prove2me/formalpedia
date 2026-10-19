-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group636
-- name    : dusart_theta_mesh_generic_group636
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:26:21.66602+00:00
-- url     : https://prove2.me/theorems/94180c9e-dd64-4cc7-a37a-3a6662a91e9c
-- title:
--   Verified numerical interval from 9059033344 to 9075810560
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9059033344, 9075810560; 9058946172797222, 9075717750135580).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group636 : DusartNumeric.GenericSpec 9059033344 9075810560 9058946172797222 9075717750135580 := by sorry
