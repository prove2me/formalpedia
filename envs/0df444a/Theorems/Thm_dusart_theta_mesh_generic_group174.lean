-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group174
-- name    : dusart_theta_mesh_generic_group174
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:32:33.061882+00:00
-- url     : https://prove2.me/theorems/181a2022-0db7-4035-9ff2-2e99cd2153f0
-- title:
--   Verified numerical interval from 1307959552 to 1324736768
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1307959552, 1324736768; 1307919231119769, 1324692615871163).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group174 : DusartNumeric.GenericSpec 1307959552 1324736768 1307919231119769 1324692615871163 := by sorry
