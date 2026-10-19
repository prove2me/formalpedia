-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group026
-- name    : dusart_theta_mesh_generic_group026
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:44.956442+00:00
-- url     : https://prove2.me/theorems/1a218e0b-96b0-4660-9bb5-7c6e9a56aaea
-- title:
--   Verified numerical interval from 154525952 to 156623104
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(154525952, 156623104; 154512129220713, 156610713264026).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group026 : DusartNumeric.GenericSpec 154525952 156623104 154512129220713 156610713264026 := by sorry
