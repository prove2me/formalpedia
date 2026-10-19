-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group027
-- name    : dusart_theta_mesh_generic_group027
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:18.843001+00:00
-- url     : https://prove2.me/theorems/72c03bdc-445c-4b70-812f-71909f414517
-- title:
--   Verified numerical interval from 156623104 to 158720256
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(156623104, 158720256; 156610713264026, 158704972339413).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group027 : DusartNumeric.GenericSpec 156623104 158720256 156610713264026 158704972339413 := by sorry
