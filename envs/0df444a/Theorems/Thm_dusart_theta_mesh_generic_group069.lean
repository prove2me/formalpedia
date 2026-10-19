-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group069
-- name    : dusart_theta_mesh_generic_group069
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:15:33.925853+00:00
-- url     : https://prove2.me/theorems/155e0d62-7fdc-4d95-bccd-ffd3dcd13b37
-- title:
--   Verified numerical interval from 288743680 to 292937984
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(288743680, 292937984; 288727196795039, 292922115152298).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group069 : DusartNumeric.GenericSpec 288743680 292937984 288727196795039 292922115152298 := by sorry
