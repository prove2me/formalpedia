-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group656
-- name    : dusart_theta_mesh_generic_group656
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:29:58.289984+00:00
-- url     : https://prove2.me/theorems/9648abf6-4363-451d-b81b-0740a20be26f
-- title:
--   Verified numerical interval from 9394577664 to 9411354880
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9394577664, 9411354880; 9394490159695874, 9411264939493626).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group656 : DusartNumeric.GenericSpec 9394577664 9411354880 9394490159695874 9411264939493626 := by sorry
