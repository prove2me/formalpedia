-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group351
-- name    : dusart_theta_mesh_generic_group351
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:52:34.604808+00:00
-- url     : https://prove2.me/theorems/f550bd35-4301-411b-8e80-018345a2f6a8
-- title:
--   Verified numerical interval from 4277526784 to 4294304000
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4277526784, 4294304000; 4277458848789031, 4294236237232646).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group351 : DusartNumeric.GenericSpec 4277526784 4294304000 4277458848789031 4294236237232646 := by sorry
