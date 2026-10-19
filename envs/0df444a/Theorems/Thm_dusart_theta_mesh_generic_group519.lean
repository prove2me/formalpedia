-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group519
-- name    : dusart_theta_mesh_generic_group519
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:12:06.833982+00:00
-- url     : https://prove2.me/theorems/6ed550a7-a693-4175-ac14-03a70ae757d1
-- title:
--   Verified numerical interval from 7096099072 to 7112876288
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7096099072, 7112876288; 7096043742345570, 7112815999221692).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group519 : DusartNumeric.GenericSpec 7096099072 7112876288 7096043742345570 7112815999221692 := by sorry
