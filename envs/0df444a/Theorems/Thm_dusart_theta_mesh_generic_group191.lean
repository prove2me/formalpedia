-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group191
-- name    : dusart_theta_mesh_generic_group191
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:35:39.121977+00:00
-- url     : https://prove2.me/theorems/f388e353-c616-4377-8d72-f33d93bbaa66
-- title:
--   Verified numerical interval from 1593172224 to 1609949440
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1593172224, 1609949440; 1593145117035717, 1609919129810472).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group191 : DusartNumeric.GenericSpec 1593172224 1609949440 1593145117035717 1609919129810472 := by sorry
