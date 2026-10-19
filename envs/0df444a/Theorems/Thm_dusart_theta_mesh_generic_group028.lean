-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group028
-- name    : dusart_theta_mesh_generic_group028
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:20.175685+00:00
-- url     : https://prove2.me/theorems/c92517d5-2bf7-42cb-b83f-b0f8f2a8c17e
-- title:
--   Verified numerical interval from 158720256 to 160817408
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(158720256, 160817408; 158704972339413, 160804854096877).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group028 : DusartNumeric.GenericSpec 158720256 160817408 158704972339413 160804854096877 := by sorry
