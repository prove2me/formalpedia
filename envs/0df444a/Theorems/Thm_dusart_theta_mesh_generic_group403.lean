-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group403
-- name    : dusart_theta_mesh_generic_group403
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:58:32.716621+00:00
-- url     : https://prove2.me/theorems/f334d60d-4ac6-4f96-8ae2-f61a83550b58
-- title:
--   Verified numerical interval from 5149942016 to 5166719232
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5149942016, 5166719232; 5149866295198825, 5166641741270139).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group403 : DusartNumeric.GenericSpec 5149942016 5166719232 5149866295198825 5166641741270139 := by sorry
