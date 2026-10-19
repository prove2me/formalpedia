-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group413
-- name    : dusart_theta_mesh_generic_group413
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:00:32.395458+00:00
-- url     : https://prove2.me/theorems/b00af734-9527-468c-bb25-ed813b0a26dc
-- title:
--   Verified numerical interval from 5317714176 to 5334491392
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5317714176, 5334491392; 5317647812683125, 5334411725302886).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group413 : DusartNumeric.GenericSpec 5317714176 5334491392 5317647812683125 5334411725302886 := by sorry
