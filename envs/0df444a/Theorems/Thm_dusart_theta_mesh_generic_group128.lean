-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group128
-- name    : dusart_theta_mesh_generic_group128
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:28:38.124674+00:00
-- url     : https://prove2.me/theorems/a84a35ee-c7c8-4ad6-a15f-1161eb61f524
-- title:
--   Verified numerical interval from 670425344 to 678813952
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(670425344, 678813952; 670406278061887, 678788959008559).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group128 : DusartNumeric.GenericSpec 670425344 678813952 670406278061887 678788959008559 := by sorry
