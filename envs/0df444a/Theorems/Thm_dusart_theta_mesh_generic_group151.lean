-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group151
-- name    : dusart_theta_mesh_generic_group151
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:30:12.18933+00:00
-- url     : https://prove2.me/theorems/97c08cb5-21bf-4558-a5e6-7b65fca5d616
-- title:
--   Verified numerical interval from 922083584 to 938860800
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(922083584, 938860800; 922059278633415, 938827934867994).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group151 : DusartNumeric.GenericSpec 922083584 938860800 922059278633415 938827934867994 := by sorry
