-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group060
-- name    : dusart_theta_mesh_generic_group060
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:14:32.688507+00:00
-- url     : https://prove2.me/theorems/a942389d-f829-4225-9158-8a096bbea27a
-- title:
--   Verified numerical interval from 250994944 to 255189248
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(250994944, 255189248; 250983698620595, 255177599586748).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group060 : DusartNumeric.GenericSpec 250994944 255189248 250983698620595 255177599586748 := by sorry
