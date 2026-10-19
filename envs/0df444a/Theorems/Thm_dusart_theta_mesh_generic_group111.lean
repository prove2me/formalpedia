-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group111
-- name    : dusart_theta_mesh_generic_group111
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:37.642987+00:00
-- url     : https://prove2.me/theorems/9f7da3d3-f020-4c78-b38e-bd5d9cfde420
-- title:
--   Verified numerical interval from 527819008 to 536207616
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(527819008, 536207616; 527791285181818, 536181549944858).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group111 : DusartNumeric.GenericSpec 527819008 536207616 527791285181818 536181549944858 := by sorry
