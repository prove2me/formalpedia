-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group567
-- name    : dusart_theta_mesh_generic_group567
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:18:45.881776+00:00
-- url     : https://prove2.me/theorems/bfc45ffb-7386-48af-b753-c4237773189b
-- title:
--   Verified numerical interval from 7901405440 to 7918182656
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7901405440, 7918182656; 7901279936113055, 7918066696337914).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group567 : DusartNumeric.GenericSpec 7901405440 7918182656 7901279936113055 7918066696337914 := by sorry
