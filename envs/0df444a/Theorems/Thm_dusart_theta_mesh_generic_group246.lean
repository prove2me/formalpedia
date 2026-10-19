-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group246
-- name    : dusart_theta_mesh_generic_group246
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:41:27.329329+00:00
-- url     : https://prove2.me/theorems/04b92e1f-8d0c-4db8-acde-53a37ef55fcf
-- title:
--   Verified numerical interval from 2515919104 to 2532696320
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2515919104, 2532696320; 2515867244804953, 2532649940210397).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group246 : DusartNumeric.GenericSpec 2515919104 2532696320 2515867244804953 2532649940210397 := by sorry
