-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group400
-- name    : dusart_theta_mesh_generic_group400
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:59:35.221912+00:00
-- url     : https://prove2.me/theorems/f163aea7-1c63-44c1-a095-a8ac4031cc21
-- title:
--   Verified numerical interval from 5099610368 to 5116387584
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5099610368, 5116387584; 5099525408083713, 5116316926602358).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group400 : DusartNumeric.GenericSpec 5099610368 5116387584 5099525408083713 5116316926602358 := by sorry
